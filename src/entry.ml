module Env = Api.Env
module T = Kernel.Term
module B = Kernel.Basic
module A = Agda
module M = Metavars
module C = Conv
module U = Unif
module D = Lvldk
module S = Kernel.Signature
module R = Kernel.Rule
module L = Lvl
open Common

let pts_empty_set = T.mk_App D.pts_m D.pts_0_n [D.pts_empty]
            
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
        
let mk_term_univ_poly te lvars =
  let new_te = cons_to_vars lvars 0 te in
  let rec add_abs t l =
    match l with
    | [] -> t
    | x :: l -> T.mk_Lam B.dloc (B.mk_ident x) (Some D.sort_ty) (add_abs t l)
  in add_abs new_te (List.rev lvars)

let mk_ty_univ_poly ty lvars =
  let new_ty = cons_to_vars lvars 0 ty in
  let rec add_pi t l =
    match l with
    | [] -> t
    | x :: l -> T.mk_Pi B.dloc (B.mk_ident x) D.sort_ty (add_pi t l)
  in add_pi new_ty (List.rev lvars)
   

let up_def_arity = ref []

let rec generate_uvars n te =
  if n = 0 then te else T.mk_App (generate_uvars (n - 1) te) D.metavar_te []
                 
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

exception Not_a_patt
       
let rec term_to_pattern t =
  let open T in
  let open R in
  match t with
  | App(Const(l, c), t1, tl) -> Pattern(l, c, List.map term_to_pattern (t1 :: tl))
  | App(DB(l, id, n), t1, tl) -> Var(l, id, n, List.map term_to_pattern (t1 :: tl))
  | Lam(l, id, _, body) -> Lambda(l, id, term_to_pattern body)
  | Const(l, c) -> Pattern(l, c, [])
  | DB(l, id, n) -> Var(l, id, n, [])
  | _ -> raise Not_a_patt

exception Todo
exception Impossible
        
let rec get_poly_vars t =
  let open T in
  (*  Format.printf "term %a@." pp_term t;*)
  match t with
  | App(_, t1, tl) ->
     let l1 = get_poly_vars t1 in
     let l2 = List.fold_left (fun acc x -> acc @ (get_poly_vars x)) [] tl in
     l1 @ l2
  | Const(_, id) when (String.get (B.string_of_ident (B.id id)) 0 = '?') ->
     [B.string_of_ident (B.id id)]
  | DB(_,_,_) -> []
  | Const(_,_) -> []
  | _ -> raise Todo

exception Non_atomic_lvl_in_lhs
       
let linearize lhs rhs =
  let open T in
  let ctx = ref [] in
  let add_var loc id n depth =
    if n < depth
    then mk_DB loc id n
    else 
      let s_id = B.string_of_ident id in
      let k = List.length !ctx in
      if List.mem s_id !ctx
      then let new_s_id = s_id ^ "_" ^ (string_of_int k) in
           ctx := new_s_id :: !ctx; mk_DB loc (B.mk_ident new_s_id) (k + depth)
      else begin ctx := s_id :: !ctx; mk_DB loc id (k + depth) end in
  let rec aux depth t =
    match t with
    | App(head, t1, tl) ->
       (* We do it in reverse order so the indices grow from right to left *)
       let tl = List.rev @@ List.map (aux depth) @@ List.rev tl in
       let t1 = aux depth t1 in
       let head = match head with
         | DB(loc, id, n) -> add_var loc id n depth
         | Const(_, name) when (B.string_of_ident (B.id name) = "M" &&
                                  B.string_of_mident (B.md name) = "pts") ->
            raise Non_atomic_lvl_in_lhs
         | _ -> head in
       mk_App head t1 tl
    | DB(loc, id, n) -> add_var loc id n depth
    | Const(_,_) -> t
    | Lam(l, id, ty_op, body) ->
       let body = aux (depth + 1) body in
       let ty_op = Option.map (aux depth) ty_op in
       mk_Lam l id ty_op body
    | _ -> raise Todo in
  let rec aux2 depth t =
    match t with
    | App(head, t1, tl) ->
       mk_App (aux2 depth head) (aux2 depth t1) (List.map (aux2 depth) tl)
    | DB(loc, id, n) ->
       if n < depth
       then t
       else begin match pos (B.string_of_ident id) (List.rev !ctx) with
            | Some x -> mk_DB loc id (x + depth)
            | None -> raise Impossible end
    | Lam(loc, id, ty_op, body) ->
       mk_Lam loc id (Option.map (aux2 depth) ty_op) (aux2 (depth + 1) body)
    | Pi (loc, id, ty, body) ->
       mk_Pi loc id (aux2 depth ty) (aux2 (depth + 1) body)
    | _ -> t in
  let lhs = aux 0 lhs in
  let rhs = aux2 0 rhs in
  (lhs, rhs, !ctx)

let rec remove_non_atomic_lvls_in_lhs t =
  let open T in
  match t with
  | App(Const(_, n1), _, [t2]) when (B.string_of_ident (B.id n1) = "M") ->
     begin
       match D.extract_lvl_set t2 with
       | None -> raise Impossible
       | Some lvl_set ->
          let t1 = L.M(0, [List.hd lvl_set]) in
          List.map (fun x -> (t1, L.M(0, [x]))) (List.tl lvl_set)
     end
  | App(_, t1, tl) ->
     let c1 = remove_non_atomic_lvls_in_lhs t1 in
     let cl = List.map remove_non_atomic_lvls_in_lhs tl in     
     List.fold_left (fun acc x -> x @ acc) c1 cl
  | DB(_, _, _) -> []
  | Const(_,_) -> []
  | Lam(_, _, ty_op, body) ->
     let body_c = remove_non_atomic_lvls_in_lhs body in
     begin
       match ty_op with
       | None -> body_c
       | Some x -> body_c @ (remove_non_atomic_lvls_in_lhs x)
     end
  | _ -> raise Not_a_patt

  

exception No_solution       
exception Def_without_type

        
        
let predicativize_entry env optim out_fmt e =
  let open Parsers.Entry in
  let sg = Api.Env.get_signature env in
  let module Pp = Api.Pp.Make (struct
               let get_name () = Env.get_name env
             end) in
  M.reset_counter ();

  match e with
  | Def(l, id, sc, opq, ty_op, te) ->
     begin
       let md_name = B.string_of_mident (Env.get_name env) in
       let id_name = B.string_of_ident id in
       Format.printf "[ %s.%s ] " (blue md_name) (blue id_name); Format.print_flush ();
       
       let ty = match ty_op with
         | Some x -> x
         | None ->
            let name = B.string_of_ident id in
            Printf.printf "Error : all Defs need to have their type, but %s has no type\n" name;
            raise Def_without_type in

       
       let te = replace_arity te in
       let ty = replace_arity ty in

       let te = M.insert_lvl_metas env te in
       let ty = M.insert_lvl_metas env ty in 

(*       Format.printf "%a@." T.pp_term ty;
       Format.printf "%a@." T.pp_term te;       *)
       
       U.cstr_eq := !Cstr.extra_cstr (md_name, id_name);

       
       let _ = C.Typing.checking sg te ty in
       Format.printf "Solving %n constraints. " (List.length !U.cstr_eq); Format.print_flush ();       
       (*       List.iter (fun (t1,t2) -> Format.printf "%s = %s @." (Lvl.string_of_lvl t1) (Lvl.string_of_lvl t2)) !U.cstr_eq;       *)
       let subst = match U.solve_cstr () with
         | None -> raise No_solution
         | Some subst -> subst in

       let ty, ty_fv =
         if optim then
             let new_ty, _ = D.apply_subst_to_term subst ty in
             (new_ty, D.get_vars_in_u subst ty)
             else D.apply_subst_to_term subst ty in

       let te, _ = D.apply_subst_to_term subst te in
       let ty = mk_ty_univ_poly ty ty_fv in
       let te = mk_term_univ_poly te ty_fv in

       Format.printf "%s@." @@ green @@
         "Solution found with " ^ (string_of_int (List.length ty_fv)) ^ " up vars.";
       
       let new_entry = Def (l, id, sc, opq, Some ty, te) in
       Format.fprintf out_fmt "%a@." Pp.print_entry new_entry;
       up_def_arity := (B.string_of_mident (Env.get_name env), B.string_of_ident id, List.length ty_fv)
                       :: !up_def_arity;
       Env.define env l id sc opq te (Some ty);
       Some new_entry
       
     end
  | Decl(l, id, sc, opq, ty) ->
     begin
       let md_name = B.string_of_mident (Env.get_name env) in
       let id_name = B.string_of_ident id in
       Format.printf "[ %s.%s ] " (blue md_name) (blue id_name); Format.print_flush ();

       let ty = replace_arity ty in
       let ty = M.insert_lvl_metas env ty in

       (*       Format.printf "%a@." T.pp_term ty;*)

       U.cstr_eq := !Cstr.extra_cstr (md_name, id_name);
(*       List.iter (fun (t1,t2) -> Format.printf "%s = %s ;" (Lvl.string_of_lvl t1) (Lvl.string_of_lvl t2)) !U.cstr_eq;
       Format.printf "@.oi %d@." (List.length !U.cstr_eq);       *)
       let _ = C.Typing.inference sg ty in

       Format.printf "Solving %n constraints. " (List.length !U.cstr_eq); Format.print_flush ();
       let subst = match U.solve_cstr () with
         | None -> raise No_solution
         | Some subst -> subst in

       let ty, ty_fv =
         if optim then
             let new_ty, _ = D.apply_subst_to_term subst ty in
             (new_ty, D.get_vars_in_u subst ty)
         else D.apply_subst_to_term subst ty in

       Format.printf "%s@." @@ green @@
         "Solution found with " ^ (string_of_int (List.length ty_fv)) ^ " up vars.";
       
       let ty = mk_ty_univ_poly ty ty_fv in

       let new_entry = Decl (l, id, sc, opq, ty) in

       Format.fprintf out_fmt "%a@." Pp.print_entry new_entry;       
       up_def_arity := (B.string_of_mident (Env.get_name env), B.string_of_ident id, List.length ty_fv)
                       :: !up_def_arity;
       Env.declare env l id sc opq ty;
       Some new_entry
       
     end
  | Rules(l, [r]) ->
     Format.printf "[ Rewrite rule ] ";
     let lhs = R.pattern_to_term r.pat in
     let lhs = replace_arity lhs in
     let lhs = M.insert_lvl_metas env lhs in
     let lhspt = term_to_pattern lhs in

     let rhs = replace_arity r.rhs in
     let rhs = M.insert_lvl_metas env rhs in
     (*     Format.printf "oi1@.";*)

     (* We use the check_rule to try to check that the rule satisfies sr. In the process, constraints 
        are generated to assure that this is indeed the case. Note that infering the type of the lhs 
        and then checking that the rhs has the same type would not work, as we do not know the types
        of the variables in the rule context. I see no clear way of infering them, thus this seems to
        be the only option to me. *)
     let _ = List.map (C.Typing.check_rule sg) [{name = r.name; ctx = r.ctx; pat = lhspt; rhs = rhs}] in
(*     let lhs_ty = C.Typing.infer sg lhs in
     C.Typing.checking sg rhs lhs_ty; *)
     (*     Format.printf "oi2@.";*)
     
     (*     List.iter (fun (x,y) -> Format.printf "%s = %s@." (Lvl.string_of_lvl x) (Lvl.string_of_lvl y)) !U.cstr_eq;*)     

     (*     Format.printf "cstr@. "; List.iter (fun (x, y) -> Format.printf "%s = %s@." (Lvl.string_of_lvl x) (Lvl.string_of_lvl y)) !U.cstr_eq;*)
     
     Format.printf "Solving %n constraints. " (List.length !U.cstr_eq); Format.print_flush ();
     let subst = match U.solve_cstr () with
       | None -> raise No_solution
       | Some subst -> subst in

     let lhs, _ = D.apply_subst_to_term subst lhs in

     let rhs, _ = D.apply_subst_to_term subst rhs in


     let cfg = Api.Meta.default_config () in
     let meta_rules = Api.Meta.parse_meta_files ["metas/remove_vars.dk"] in
     Api.Meta.add_rules cfg meta_rules;

     let lhs = Api.Meta.mk_term cfg lhs in
     let rhs = Api.Meta.mk_term cfg rhs in
     
     U.cstr_eq := remove_non_atomic_lvls_in_lhs lhs;
                  Format.printf "%a@." T.pp_term lhs;
          List.iter (fun (x,y) -> Format.printf "%s = %s@." (Lvl.string_of_lvl x) (Lvl.string_of_lvl y)) !U.cstr_eq;
     let remove_non_alvl_subst = match U.solve_cstr () with
       | None -> raise No_solution
       | Some subst -> subst in

     let lhs, _ = D.apply_subst_to_term remove_non_alvl_subst lhs in
                  Format.printf "%a@." T.pp_term lhs;
     let rhs, _ = D.apply_subst_to_term remove_non_alvl_subst rhs in

     let lhs = Api.Meta.mk_term cfg lhs in
     let rhs = Api.Meta.mk_term cfg rhs in
                  Format.printf "%a@." T.pp_term lhs;
     

     let vars = List.rev @@ remove_duplicates @@ get_poly_vars lhs in
     
     let lhs = cons_to_vars (List.rev vars) (List.length r.ctx) lhs in
     let rhs = cons_to_vars (List.rev vars) (List.length r.ctx) rhs in     

     let lhs, rhs, ctx = linearize lhs rhs in
     (*     Format.printf "%a --> %a@." T.pp_term lhs T.pp_term rhs;*)
     let lhspt = term_to_pattern lhs in     

     let ctx = List.map (fun s -> B.dloc, B.mk_ident s, None) (List.rev ctx) in

     let new_entry = Rules(l, [{name = r.name; ctx = ctx; pat = lhspt; rhs = rhs}]) in
     Format.fprintf out_fmt "%a@." Pp.print_entry new_entry;       

     List.iter (fun (_,s,_) -> Format.printf "%s " (B.string_of_ident s)) r.ctx;
     (*     Format.printf "@.oi3@.";*)
     let _ = Env.add_rules env [{name = r.name; ctx = ctx; pat = lhspt; rhs = rhs}] in
     (*     Format.printf "oi4@.";     *)
     Format.printf "%s@." (green "Ok");
     Some new_entry
     
(*     Format.printf "We have the following constrains: @.";
     List.iter (fun (x, y) -> Format.printf "%s = %s@." (Lvl.string_of_lvl x) (Lvl.string_of_lvl y))
       !U.cstr_eq;
     U.cstr_eq := [];*)

  | Rules(_, _) -> Format.printf "TODO@."; None
  | _ -> None
