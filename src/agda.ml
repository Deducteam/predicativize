module T = Kernel.Term
module B = Kernel.Basic
module Env = Api.Env
open Common

let qname_to_name = ref @@ fun (_, _) -> None
let const_names = ref []

                                       
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
     let ident = sanitize @@ (B.string_of_ident var) in
     let ident = if List.mem ident !const_names then ident ^ "-v" else ident in
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
     
  | _ -> None 
  
and dklvl_to_agda_lvl t =
  let open T in
  match t with
  | DB(_, var, _) ->
     let ident = sanitize @@ B.string_of_ident var in
     let ident = if List.mem ident !const_names then ident ^ "-v" else ident in
     Some (Lvar ident)
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

let fresh_var = ref 0
              
  
let rec dkterm_to_term n te =
  let open T in
  match te with

  (* te = pts.Prod _ _ ta (var => body_b) *)    
  | App(Const(_,pi), _, [_; ta; Lam(_, var, _, body_b)]) when
         (B.string_of_mident (B.md pi) = "pts" && B.string_of_ident (B.id pi) = "Prod") ->
     let* ta = dkterm_to_term n ta in
     let* tb = dkterm_to_term (n + 1) body_b in
     let ident = sanitize @@ (B.string_of_ident var) in
     let ident = if List.mem ident !const_names then ident ^ "-v" else ident in
     (*     Format.printf "%s@." ident;*)
     (*     List.iter (fun x -> Format.printf "%s " x) !const_names; Format.printf "@.";*)
     if ident = "x-free"
     then Some (A_Arr (ta, tb))
     else Some (A_Pi (ta, ident, tb))

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
     let ident = sanitize @@ (B.string_of_ident ident) in
     let ident = if List.mem ident !const_names then ident ^ "-v" else ident in
     Some (A_Lam(ident, ty_op, te))

  | DB(_, ident, _) ->
     let is_lvl_var = String.get (B.string_of_ident ident) 0 = '?' in
     let ident = sanitize @@ (B.string_of_ident ident) in
     let ident = if List.mem ident !const_names then ident ^ "-v" else ident in
     if is_lvl_var
     then Some (A_Lvl (Lvar ident))
     else Some (A_Var ident)

  | Const(_, cst) when
         (B.string_of_mident (B.md cst) = "pts" && B.string_of_ident (B.id cst) = "Prod") ->
     let n = string_of_int !fresh_var in
     fresh_var := 1 + !fresh_var;
     Some(A_Lam("sA",Some A_Lty,
                A_Lam("sB",Some A_Lty,
                      A_Lam("A",Some (A_Set (Lvar "sA")),
                            A_Lam("B", Some ( A_Pi(A_Var "A", "NotImportant", A_Set (Lvar "sB"))),
                                  A_Pi(A_Var "A", "VAR" ^ n,
                                       A_App(A_Var "B", A_Var ("VAR" ^ n), [])))))))
     

  | Const(_, cst) ->
     let md, id = (sanitize @@ B.string_of_mident @@ B.md cst,
                   B.string_of_ident  @@ B.id cst) in
     if not (md = !md_name) then  import_list := md :: !import_list;
     begin match !qname_to_name (md, id) with
       | Some x -> Some (A_Cst (None, x))
       | None   -> assert false
     end
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
    let ident = sanitize @@ (B.string_of_ident ident) in
    let ident = if List.mem ident !const_names then ident ^ "-v" else ident in
    let* t2 = dkty_to_ty (n + 1) t2 in
    Some (A_Pi (A_Lty, ident, t2))

  (* te = (ident : t1) -> t2 *)
  (* should not happen in the good cases *)
  | Pi(_, ident, t1, t2) ->
     (*     let ident = sanitize @@ (B.string_of_ident ident) ^ "-" ^ string_of_int n in*)
    let ident = sanitize @@ (B.string_of_ident ident)  in
    let ident = if List.mem ident !const_names then ident ^ "-v" else ident in
    let* t2 = dkty_to_ty (n + 1) t2 in
    let* t1 = dkty_to_ty n t1 in
    Some (A_Pi (t1, ident, t2))

  | App(Const(_,u), t, []) when
         (B.string_of_mident (B.md u) = "pts" && B.string_of_ident (B.id u) = "U") ->
     let* l = dklvl_to_agda_lvl t in
     Some (A_Set l)
  | Const(_, ty_lvl) when
         (B.string_of_mident (B.md ty_lvl) = "pts" && B.string_of_ident (B.id ty_lvl) = "Lvl") ->
     Some (A_Lty)
  | Const(_, cst) ->
     let md, id = (sanitize @@ B.string_of_mident @@ B.md cst,
                   B.string_of_ident  @@ B.id cst) in
     (*    Format.printf "%s.@.%s.@." md !md_name;*)
     if not (md = !md_name) then  import_list := md :: !import_list;
     begin match !qname_to_name (md, id) with
       | Some x -> Some (A_Cst (None, x))
       | None   -> assert false
     end
  | _ -> None

       
type agda_rew = {ctx : (string * agda_te) list; lhs : agda_te; rhs : agda_te}
       
let dkrew_to_rew (r : Kernel.Rule.partially_typed_rule) =
  let* ctx =
    all_some_list_to_some_list @@
      List.map
        (fun (_, id, ty_op) ->
          let* ty = ty_op in
          let* agda_ty = dkty_to_ty 0 ty in
          Some (sanitize @@ (B.string_of_ident id), agda_ty))
        r.ctx in
  let* lhs = dkterm_to_term 0 @@ Kernel.Rule.pattern_to_term r.pat in
  let* rhs = dkterm_to_term 0 r.rhs in
  Some {ctx = ctx; lhs = lhs; rhs = rhs}

let pp_rew_counter = ref 0
  
let pp_agda_rew fmt r =
(*  Format.fprintf fmt "postulate rewrite-rule-%s : " (string_of_int !pp_rew_counter);
  List.iter (fun (id, ty) -> Format.fprintf fmt "(%s : %a) -> " id pp_agda_te ty) r.ctx;*)
  Format.fprintf fmt "-- %a --> %a@." pp_agda_te r.lhs pp_agda_te r.rhs;
  (*  Format.fprintf fmt "{-# REWRITE rewrite-rule-%s #-}" (string_of_int !pp_rew_counter);*)
  pp_rew_counter := 1 + !pp_rew_counter

type agda_entry =
  | A_Def  of string * agda_te * agda_te
  | A_Decl of string * agda_te
  | A_Rew  of agda_rew

let pp_entry fmt e =
  let open Format in
  match e with
  | A_Def (n, ty, te) ->
     fprintf fmt "%s : %a\n" n pp_agda_te ty;
     fprintf fmt "%s = %a\n" n pp_agda_te te     
  | A_Decl (n, ty) ->
     fprintf fmt "postulate %s : %a\n" n pp_agda_te ty
  | A_Rew r -> fprintf fmt "%a@." pp_agda_rew r

let gen_unique_name old_id =
  (*  Format.printf "%s@." old_id;*)
  let id = ref (sanitize old_id) in
  (* we add as many ' as necessary so the name becomes unique *)
  while List.mem !id !const_names do
    id := !id ^ "'"
  done;
  let old_qname_to_name = !qname_to_name in
  let id = !id in
  let md_name = !md_name in
  (qname_to_name :=
     fun (s_md,s_id) ->
     if s_md = md_name && s_id = old_id
     then Some id else old_qname_to_name (s_md, s_id));
  const_names := id :: !const_names;
  id
             
let dkentry_to_entry e =
  let open Parsers.Entry in
  match e with
  | Def(_, id, _, _, Some ty, te) ->
     let* ty = dkty_to_ty 0 ty in
     let* te = dkterm_to_term 0 te in
     (*     Format.printf "oi@.";*)
     let id = gen_unique_name @@ B.string_of_ident id in
     Some (A_Def (id, ty, te))
  | Decl(_, id, _, _, ty) ->
     let* ty = dkty_to_ty 0 ty in
     (*     Format.printf "oi@.";     *)
     let id = gen_unique_name @@ B.string_of_ident id in     
     Some (A_Decl (id, ty))
  | Rules(_, [r]) -> begin
     match dkrew_to_rew r with
     | Some x -> Some (A_Rew x)
     | None -> Format.printf "Problem with rule %a@."
                 Parsers.Entry.pp_entry (Parsers.Entry.Rules (B.dloc, [r])); None end
  | _ -> None

type agda_file_element =
  | A_Entry  of agda_entry
  | A_Import of string

let pp_file fmt agda_file =
  let open Format in
  (*  fprintf fmt "{-# OPTIONS --rewriting #-}@.";
  fprintf fmt "open import Agda.Builtin.Equality using (_≡_)@.";
  fprintf fmt "open import Agda.Builtin.Equality.Rewrite@.";*)
  fprintf fmt "open import Agda.Primitive@.";  
  
  List.fold_left (fun () e ->
      match e with
      | A_Import s -> fprintf fmt "open import %s@." s
      | A_Entry e -> fprintf fmt "%a@." pp_entry e
    ) () agda_file
              
let dkfile_to_file md_name' list_entry =
  md_name := md_name';
  import_list := [];
  let list_entry =
    List.rev @@
    List.fold_left
      (fun acc_entries e ->
        match dkentry_to_entry e with
        | Some new_e -> new_e :: acc_entries
        | None -> acc_entries
      ) [] list_entry in
  let list_import = remove_duplicates !import_list in
  (List.map (fun x -> A_Import x) list_import) @ (List.map (fun e -> A_Entry e) list_entry)

                                                   
