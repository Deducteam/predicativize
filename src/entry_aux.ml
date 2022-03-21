module Env = Api.Env
module T = Kernel.Term
module B = Kernel.Basic
module D = Lvldk
module L = Lvl
open Common

let pts_empty_set = T.mk_App D.pts_m D.pts_0_n [D.pts_empty]

(* [cons_to_vars lvars depth te] converts in [te] the metavariable constants specified in [lvars] 
 to variables. The db indices start from the value [depth]. The metavariables not specified in [lvars]
 are set to Empty. *)
let rec cons_to_vars lvars depth te =
  match te with
  | T.Const (_, var_name) ->
     let var_name = B.string_of_ident @@ B.id var_name in
     if String.get var_name 0 != '?' then te
     else begin match pos var_name lvars with
          | None -> pts_empty_set
          | Some n -> T.mk_DB B.dloc (B.mk_ident var_name) (n + depth) end
  | T.App (f, a1, al) ->
     T.mk_App
       (cons_to_vars lvars depth f)
       (cons_to_vars lvars depth a1)
       (List.map (cons_to_vars lvars depth) al)
  | T.Lam (l, id, t, body) ->
     T.mk_Lam l id
       (Option.map (cons_to_vars lvars depth) t)
       (cons_to_vars lvars (1 + depth) body)
  | T.Pi (l, id, a, b) ->
     T.mk_Pi l id
       (cons_to_vars lvars depth a)
       (cons_to_vars lvars (1 + depth) b)
  | _ -> te

(* [mk_term_univ_poly te lvars] returns lambda lvars. te *)       
let mk_term_univ_poly te lvars =
  let new_te = cons_to_vars lvars 0 te in
  let rec add_abs t l =
    match l with
    | [] -> t
    | x :: l -> T.mk_Lam B.dloc (B.mk_ident x) (Some D.sort_ty) (add_abs t l)
  in add_abs new_te (List.rev lvars)

(* [mk_term_univ_poly te lvars] returns forall lvars. te *)          
let mk_ty_univ_poly ty lvars =
  let new_ty = cons_to_vars lvars 0 ty in
  let rec add_pi t l =
    match l with
    | [] -> t
    | x :: l -> T.mk_Pi B.dloc (B.mk_ident x) D.sort_ty (add_pi t l)
  in add_pi new_ty (List.rev lvars)
   
(* [generate_uvars n te] generates the term (te var var ... var), where there are n occurences of var *)
let rec generate_uvars n te =
  if n = 0 then te else T.mk_App (generate_uvars (n - 1) te) D.metavar_te []

let up_def_arity = ref []
(* [replace_arity te] replaces in [te] each occurence of md.id by md.id var .. var (n times var), 
   when (md, id, n) is an element of !up_def_arity  *)                 
let rec replace_arity te =
  match te with
  | T.Const(_,n) ->
     let var_name = B.string_of_ident @@ B.id n in
     let md_name = B.string_of_mident @@ B.md n in
     let find_in_list =
       List.fold_left
         (fun acc (md, id, t) ->
           if id = var_name && md = md_name then Some t else acc)
         None !up_def_arity in
     begin
       match find_in_list with
       | None -> te
       | Some n -> generate_uvars n te end
  | T.App (f, a1, al) ->
     T.mk_App (replace_arity f) (replace_arity a1) (List.map replace_arity al)
  | T.Lam (l, id, t, body) ->
     T.mk_Lam l id (Option.map replace_arity t) (replace_arity body)
  | T.Pi (l, id, a, b) ->
     T.mk_Pi l id (replace_arity a) (replace_arity b)
  | _ -> te

(* [get_univs_in_u te] returns a list of the levels appearing in the arguments of pts.u in [te]. 
   If some lvl appears somewhere else (eg Nat lzero), then returns None. *)
let rec get_univs_in_u te : Lvl.level list option =
  if D.extract_lvl None te != None then None
  else
    let open T in
    match te with
    | App (Const (_, name_u), univ, []) when
           ((B.string_of_ident @@ B.id name_u = "u" || B.string_of_ident @@ B.id name_u = "U")
            && B.string_of_mident @@ B.md name_u = "pts") ->
       let* lvl = D.extract_lvl None univ in
       Some [lvl]
    | App (Const (_, prod), _, [_; t1; t2]) when
           (B.string_of_ident @@ B.id prod = "Prod" && B.string_of_mident @@ B.md prod = "pts") ->
       let* u1 = get_univs_in_u t1 in
       let* u2 = get_univs_in_u t2 in
       Some (remove_duplicates @@ u1 @ u2)
    | App (Const (_, el), _, [t]) when
           (B.string_of_ident @@ B.id el = "El" && B.string_of_mident @@ B.md el = "pts") ->
       get_univs_in_u t
    | App (t1, t2, tl) ->
       let* u1 = get_univs_in_u t1 in
       let* u2 = get_univs_in_u t2 in
       let* ul = List.fold_left
                   (fun acc x ->
                     match x, acc with
                     | None, _ | _, None -> None
                     | Some x, Some l -> Some (x @ l))
                   (Some [])
                   @@ List.map get_univs_in_u tl in
       Some (remove_duplicates @@ u1 @ u2 @ ul)
    | Lam (_, _, ty_op, body) ->
       let* uty = match ty_op with
         | None -> Some []
         | Some ty -> get_univs_in_u ty in
       let* ubody = get_univs_in_u body in
       Some (remove_duplicates @@ uty @ ubody)
    | Pi (_, _, t1, t2) ->
       let* u1 = get_univs_in_u t1 in
       let* u2 = get_univs_in_u t2 in
       Some (remove_duplicates @@ u1 @ u2)
    | _ -> Some []

let get_type_former_predicativity_cstrs te =
  let rec aux other_univs te =
    let open T in
    match te with
    | App (Const (_, name_u), Const(_, metavar), []) when
           ((B.string_of_ident @@ B.id name_u = "u" || B.string_of_ident @@ B.id name_u = "U" )
            && B.string_of_mident @@ B.md name_u = "pts"
            && String.get (B.string_of_ident @@ B.id metavar) 0 = '?') ->
       let t1 = L.list_to_max @@ remove_duplicates @@ other_univs in
       let t2 = L.M(0, [L.S(0, B.string_of_ident @@ B.id metavar)]) in
       Some (t1, t2)
    | App (Const (_, prod), _, [_; t1; t2]) when
           (B.string_of_ident @@ B.id prod = "Prod" && B.string_of_mident @@ B.md prod = "pts") ->
       let* u1 = get_univs_in_u t1 in
       aux (other_univs @ u1) t2
    | App (Const (_, el), _, [t]) when
           (B.string_of_ident @@ B.id el = "El" && B.string_of_mident @@ B.md el = "pts") ->
       aux other_univs t
    | App (t1, t2, []) ->
       let* u1 = get_univs_in_u t1 in
       aux (other_univs @ u1) t2
    | App (t1, t2, tl) ->
       let* u1 = get_univs_in_u t1 in
       let* u2 = get_univs_in_u t2 in
       let* ul = List.fold_left (fun acc x ->
                     match x, acc with
                     | None, _ | _, None -> None
                     | Some x, Some l -> Some (x @ l))
                   (Some [])
                 @@ List.map get_univs_in_u @@ List.tl tl in
       aux (other_univs @ u1 @ u2 @ ul) (List.hd tl)
    | Lam (_, _, ty_op, body) ->
       let* uty = match ty_op with
         | None -> Some []
         | Some ty -> get_univs_in_u ty in
       aux (other_univs @ uty) body
    | Pi (_, _, t1, t2) ->
       let* u1 = get_univs_in_u t1 in
       aux (other_univs @ u1) t2
    | _ -> None in
  aux [] te








           
