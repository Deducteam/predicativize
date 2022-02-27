module Env = Api.Env
module T = Kernel.Term
module B = Kernel.Basic
module M = Metavars
module C = Conv
module U = Unif
module D = Lvldk

exception No_solution
exception Todo
exception Error_while_def_or_decl                       

let pts_empty_set = T.mk_App D.pts_m D.pts_0_n [D.pts_empty]

let rec pos x l =
  match l with
  | [] -> None
  | y :: l -> if y = x then Some 0
              else Option.map (fun a -> 1 + a) (pos x l)
            
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
   

        
let predicativize_entry env out_fmt e =
  let open Parsers.Entry in
  let sg = Api.Env.get_signature env in
  M.open_metavar_oc_and_reset_counter ();  
  match e with
  | Def(l, id, sc, opq, ty_op, te) ->
     begin
       let te = M.insert_lvl_metas te in
       M.dkcheck_metavar ();
       let ty_op = Option.map M.insert_lvl_metas ty_op in
       let res_ty = match ty_op with
         | None -> C.Typing.inference sg te
         | Some ty -> C.Typing.checking sg te ty; ty
       in
       let subst = match U.solve_cstr () with
         | None -> raise No_solution
         | Some subst -> subst in ()
(*       let te = apply_lvl_subst subst te in
       let res_ty = apply_lvl_subst subst res_ty in
       let lvl_fv = get_lvl_free_vars te res_ty in
       let te = set_vars_not_in_ty_to_zero lvl_fv te in
       let te = mk_term_univ_poly te lvl_fv in
       let res_ty = mk_ty_univ_poly res_ty lvl_fv in
       let new_entry = Def(l, id, sc, opq, res_ty, te) in
       try
         Env.define env l id sc opq res_ty te
       with _ -> raise Error_while_def_or_decl*)
     end
  | Decl(l, id, sc, opq, ty) ->
     begin
       let ty = M.insert_lvl_metas ty in
       M.dkcheck_metavar ();
       let sort = C.Typing.inference sg ty in
       let subst = match U.solve_cstr () with
         | None -> raise No_solution
         | Some subst -> subst in
       let ty, ty_fv = D.apply_subst_to_term subst ty in
       T.pp_term Format.std_formatter ty;
       Format.printf "@.";
       let ty = mk_ty_univ_poly ty ["?1"] in
       (*       let ty = C.RE.snf sg ty in*)
       Format.printf "The term is = ";       
       T.pp_term Format.std_formatter ty;
       Format.printf "@.";       
       List.iter (Printf.printf "%s ") ty_fv
(*       let te = apply_lvl_subst subst te in
       let res_ty = apply_lvl_subst subst res_ty in
       let lvl_fv = get_lvl_free_vars te res_ty in
       let te = set_vars_not_in_ty_to_zero lvl_fv te in
       let te = mk_term_univ_poly te lvl_fv in
       let res_ty = mk_ty_univ_poly res_ty lvl_fv in
       let new_entry = Def(l, id, sc, opq, res_ty, te) in
       try
         Env.define env l id sc opq res_ty te
       with _ -> raise Error_while_def_or_decl*)
     end    
  | _ -> raise Todo
