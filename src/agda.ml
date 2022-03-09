module T = Kernel.Term
module B = Kernel.Basic
module Env = Api.Env
open Common
   
type agda_lvl =
  | Lzero
  | Lsucc of agda_lvl
  | Lmax of agda_lvl * agda_lvl
  | Lvar of string

let rec pp_agda_lvl fmt t =
  let open Format in
  match t with
  | Lzero -> fprintf fmt "lzero"
  | Lsucc t -> fprintf fmt "lsuc %a" pp_agda_lvl_par t
  | Lmax (t1, t2) -> fprintf fmt "%a ⊔ %a" pp_agda_lvl_par t1 pp_agda_lvl_par t2
  | Lvar s -> fprintf fmt "%s" s
and pp_agda_lvl_par fmt t =
  let open Format in  
  match t with
  | Lzero | Lvar _ -> pp_agda_lvl fmt t
  | _ -> fprintf fmt "(%a)" pp_agda_lvl t

let simplify t =
  match t with
  | Lmax (Lzero, x) -> x
  | Lmax (x, Lzero) -> x
  | _ -> t
            
let rec n_succ t n =
  if n = 0 then t else Lsucc (n_succ t (n - 1))

let rec extract_int t =
  let open T in
  match t with
  | App(Const(_, n1), t1, []) when (B.string_of_ident (B.id n1) = "S_N") ->
     let* m = extract_int t1 in
     Some (1 + m)
  | Const(_, n) when (B.string_of_ident (B.id n) = "0_N") -> Some 0
  | _ -> None 

let rec extract_lvl_set t =
  let open T in
  match t with

  | Const (_, empty) when (B.string_of_ident (B.id empty) = "Empty") ->
     Some Lzero
    
  | App(Const(_, m), n, [t]) when
         (B.string_of_mident (B.md m) = "pts" && B.string_of_ident (B.id m) = "M") ->
     let* t = extract_lvl_set t in
     let* n = extract_int n in     
     Some (Lmax (n_succ Lzero n, t)) 
    
  | App(Const(_, s), n, [DB(_,var, _)]) when
         (B.string_of_ident (B.id s) = "S" && String.get (B.string_of_ident var) 0 = '?') ->
     let* n = extract_int n in
     let ident = B.string_of_ident var in
     Some (n_succ (Lvar ident) n)

  (* sometimes we can have nested Ms, as in M 1 [S 0 x; S 2 (M 3 [])] *)
  | App(Const(_, s), n, [t]) when B.string_of_ident (B.id s) = "S" ->
     let* n = extract_int n in
     let* t = dklvl_to_agda_lvl t in
     Some (n_succ t n)
     
  | App(Const(_, n), t1, [t2]) when (B.string_of_ident (B.id n) = "Union") ->
     let* t1 = extract_lvl_set t1 in
     let* t2 = extract_lvl_set t2 in
     Some (Lmax (t1, t2))
     
  | _ -> pp_term Format.std_formatter t; None 
  
and dklvl_to_agda_lvl t =
  let open T in
  match t with
  | Const(_, lzero) when
         (B.string_of_mident (B.md lzero) = "pts" && B.string_of_ident (B.id lzero) = "lzero") ->
     Some Lzero
  | App(Const(_, lsucc), t, []) when
         (B.string_of_mident (B.md lsucc) = "pts" && B.string_of_ident (B.id lsucc) = "lsucc") ->
     let* t = dklvl_to_agda_lvl t in
     Some (Lsucc t)
  | App(Const(_, lmax), t1, [t2]) when
         (B.string_of_mident (B.md lmax) = "pts" && B.string_of_ident (B.id lmax) = "lmax") ->
     let* t1 = dklvl_to_agda_lvl t1 in
     let* t2 = dklvl_to_agda_lvl t2 in     
     Some (Lmax (t1, t2))
  | App(Const(_, m), n, [Const(_, empty)]) when
         (B.string_of_mident (B.md m) = "pts" && B.string_of_ident (B.id m) = "M"
          && B.string_of_mident (B.md empty) = "pts" && B.string_of_ident (B.id empty) = "Empty") ->
     let* n = extract_int n in     
     Some (n_succ Lzero n)
  | App(Const(_, m), n, [t]) when
         (B.string_of_mident (B.md m) = "pts" && B.string_of_ident (B.id m) = "M") ->
     let* t = extract_lvl_set t in
     let* n = extract_int n in     
     Some (Lmax (n_succ Lzero n, t))
  | _ -> None 
          
type agda_te =
  | A_Set of agda_lvl
  | A_Lty 
  | A_App of agda_te * agda_te * agda_te list
  | A_Lam of string * agda_te option * agda_te
  | A_Pi  of agda_te * string * agda_te
  | A_Arr of agda_te * agda_te
  | A_Lvl of agda_lvl
  | A_Var of string
  | A_Cst of string option * string

exception Impossible
           
let rec pp_agda_te fmt t =
  let open Format in
  match t with
  | A_Set (Lvar _ as lvl) -> fprintf fmt "Set %a" pp_agda_lvl lvl
  | A_Set lvl -> fprintf fmt "Set (%a)" pp_agda_lvl lvl
  | A_App (t1, t2, []) ->
     fprintf fmt "%a %a" pp_agda_te_par t1 pp_agda_te_par t2
  | A_App (t1, t2, tl) ->
     fprintf fmt "%a %a " pp_agda_te_par t1 pp_agda_te_par t2;
     pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ") pp_agda_te_par fmt tl 
  | A_Lam (_, Some A_Lty, _) -> fprintf fmt "λ (%a" pp_agda_te_lvl t    
  | A_Lam (n, None, t) -> fprintf fmt "λ %s -> %a" n pp_agda_te t
  | A_Lam (n, Some ty, t) -> fprintf fmt "λ (%s : %a) -> %a" n pp_agda_te ty pp_agda_te t
  | A_Pi (A_Lty, _, _) -> fprintf fmt "(%a" pp_agda_te_lvl t
  | A_Pi (t1, n, t2) -> fprintf fmt "(%s : %a) -> %a" n pp_agda_te t1 pp_agda_te t2
  | A_Arr (t1, t2) -> fprintf fmt "%a -> %a" pp_agda_te_par t1 pp_agda_te t2
  | A_Lvl t -> fprintf fmt "%a" pp_agda_lvl t
  | A_Var n -> fprintf fmt "%s" n
  | A_Lty -> fprintf fmt "Level"
  | A_Cst (None, id) -> fprintf fmt "%s" id
  | A_Cst (Some md, id) -> fprintf fmt "%s.%s" md id
and pp_agda_te_par fmt t =
  let open Format in
  match t with
  | A_Cst _ | A_Var _ -> fprintf fmt "%a" pp_agda_te t
  | A_Lvl t -> pp_agda_lvl_par fmt t
  | _ -> fprintf fmt "(%a)" pp_agda_te t
and pp_agda_te_lvl fmt t =
  let open Format in
  match t with
  | A_Pi(A_Lty, n, (A_Pi(A_Lty,_,_) as t)) | A_Lam(n, Some A_Lty, (A_Lam(_,Some A_Lty,_) as t)) ->
     fprintf fmt "%s %a" n pp_agda_te_lvl t
  | A_Pi(A_Lty, n, t) | A_Lam(n, Some A_Lty, t) ->
     fprintf fmt "%s : Level) -> %a" n pp_agda_te t
  | _ -> raise Impossible
       
    

let md_name = ref ""
let import_list = ref []
  
let rec dkterm_to_term n te =
  let open T in
  match te with

  (* te = pts.Prod _ _ ta (var => body_b) *)    
  | App(Const(_,pi), _, [_; ta; Lam(_, var, _, body_b)]) when
         (B.string_of_mident (B.md pi) = "pts" && B.string_of_ident (B.id pi) = "Prod") ->
     let* ta = dkterm_to_term n ta in
     let* tb = dkterm_to_term (n + 1) body_b in
     let ident = B.string_of_ident var in
     if ident = "x_free"
     then Some (A_Arr (ta, tb))
     else
       let ident = sanitize @@ ident ^ "-" ^ string_of_int n in
       Some (A_Pi (ta, ident, tb))

  (* te = pts.u lvl_exp *)
  | App(Const(_,u), lvl_exp, []) when
         (B.string_of_mident (B.md u) = "pts" && B.string_of_ident (B.id u) = "u") ->
     let* lvl_exp = dklvl_to_agda_lvl lvl_exp in
     Some (A_Set (simplify lvl_exp))

  | App(Const(_,m), _, _) when
         (B.string_of_mident (B.md m) = "pts" &&
            (B.string_of_ident (B.id m) = "M" || B.string_of_ident (B.id m) = "lzero"
             || B.string_of_ident (B.id m) = "lsucc" || B.string_of_ident (B.id m) = "lmax")) ->
     let* lvl_exp = dklvl_to_agda_lvl te in
     Some (A_Lvl (simplify lvl_exp))

  | App(t1, t2, t_list) ->
     let* t1 = dkterm_to_term n t1 in
     let* t2 = dkterm_to_term n t2 in     
     let rec aux = function
       | (Some x) :: l ->
          let* l' = aux l in
          Some (x :: l')
       | None :: _ -> None
       | [] -> Some []
     in
     let* t_list = aux (List.map (dkterm_to_term n) t_list) in
     Some (A_App (t1, t2, t_list))

  | Lam(_, ident, ty_op, te) ->
     let* te = dkterm_to_term (n + 1) te in
     let* ty_op = match ty_op with
       | None -> Some None
       | Some (Const(_, lty)) when
              (B.string_of_mident (B.md lty) = "pts" && B.string_of_ident (B.id lty) = "Lvl") ->
          Some (Some A_Lty)
       | Some x ->
          Option.bind (dkty_to_ty n x) (fun res -> Some (Some res)) in
     let ident = sanitize @@ B.string_of_ident ident in
     (* We need to annotate the non-level variables with the depth, because 
        they migth not be unique. However, this is not needed for level variables,
        as they are all unique. *)
     let ident = if String.get ident 0 = '?' then ident else ident ^ "-" ^ string_of_int n in
     Some (A_Lam(ident, ty_op, te))

  | DB(_, ident, num) ->
     let ident = sanitize @@ (B.string_of_ident ident) ^ "-" ^ string_of_int (n - num - 1) in 
     Some (A_Var ident)

  | Const(_, cst) ->
     let name = sanitize @@ B.string_of_ident (B.id cst) in
     let modu = sanitize @@ B.string_of_mident (B.md cst) in
     let modu = if modu = !md_name then None
                else (import_list := modu :: !import_list; Some modu) in
     Some (A_Cst (modu, name))     
     
  | _ -> None

and dkty_to_ty n te =
  let open T in
  match te with

  (* te = pts.El _ t' *)    
  | App(Const(_,el), _, [t']) when
         (B.string_of_mident (B.md el) = "pts" && B.string_of_ident (B.id el) = "El") ->
     dkterm_to_term n t'

  (* te = (ident : pts.Lvl) -> t2 *)
  | Pi(_, ident, Const(_,lvl), t2) when
         (B.string_of_mident (B.md lvl) = "pts" && B.string_of_ident (B.id lvl) = "Lvl") ->
     let ident = sanitize @@ B.string_of_ident ident in
     let* t2 = dkty_to_ty (n + 1) t2 in
     Some (A_Pi (A_Lty, ident, t2))

  (* te = (ident : t1) -> t2 *)
  (* should not happen in the good cases *)
  | Pi(_, ident, t1, t2) ->
     let ident = sanitize @@ B.string_of_ident ident in
     let* t2 = dkty_to_ty (n + 1) t2 in
     let* t1 = dkty_to_ty n t1 in     
     Some (A_Pi (t1, ident, t2))   
  | _ -> None

type agda_entry =
  | A_Def  of string * agda_te * agda_te
  | A_Decl of string * agda_te

let pp_entry fmt e =
  let open Format in
  match e with
  | A_Def (n, ty, te) ->
     fprintf fmt "%s : %a\n" n pp_agda_te ty;
     fprintf fmt "%s = %a\n" n pp_agda_te te     
  | A_Decl (n, ty) ->
     fprintf fmt "postulate %s : %a\n" n pp_agda_te ty

let dkentry_to_entry e =
  let open Parsers.Entry in
  match e with
  | Def(_, id, _, _, Some ty, te) ->    
     let* ty = dkty_to_ty 0 ty in
     let* te = dkterm_to_term 0 te in
     let id = sanitize @@ B.string_of_ident id in
     Some (A_Def (id, ty, te))
  | Decl(_, id, _, _, ty) ->    
     let* ty = dkty_to_ty 0 ty in
     let id = sanitize @@ B.string_of_ident id in
     Some (A_Decl (id, ty))
  | _ -> None


type agda_file_element =
  | A_Entry  of agda_entry
  | A_Import of string

let pp_file fmt agda_file =
  let open Format in
  List.fold_left (fun () e ->
      match e with
      | A_Import s ->
         if s = "Agda.Primitive"
         then fprintf fmt "open import %s@." s
         else fprintf fmt "import %s@." s
      | A_Entry e -> fprintf fmt "%a@." pp_entry e
    ) () agda_file
              
let dkfile_to_file md_name' list_entry =
  md_name := sanitize @@ md_name';
  import_list := [];
  let list_entry =
    List.fold_left
      (fun acc_entries e ->
        match dkentry_to_entry e with
        | Some new_e -> new_e :: acc_entries
        | None -> acc_entries
      ) [] list_entry in
  let list_import = remove_duplicates @@ "Agda.Primitive" :: !import_list in
  (List.map (fun x -> A_Import x) list_import) @ (List.map (fun e -> A_Entry e) list_entry)

                                                   
