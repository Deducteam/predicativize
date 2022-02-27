module Env = Api.Env
module T = Kernel.Term
module B = Kernel.Basic
module M = Metavars
module C = Conv
module U = Unif
module D = Lvldk
module S = Kernel.Signature         

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
                 
let predicativize_entry env out_fmt e =
  let open Parsers.Entry in
  Format.printf "here@.";
  (* ATTENTION here i have to reload the env in order to have the metavariables, but
     then i lose the other things i added to the signature. we thus need to keep them in
     a separate list and add them each time *)
  let env = Env.init (Parsers.Parser.input_from_file "test.dk") in
  let sg = Api.Env.get_signature env in
  M.open_metavar_oc_and_reset_counter ();  
  match e with
  | Def(l, id, sc, opq, ty_op, te) ->
     begin
       Format.printf "test1@.";       
       let ty = match ty_op with
         | Some x -> x
         | None -> C.Typing.inference sg te in
       Format.printf "test2@.";
       let te = replace_arity te in
       let ty = replace_arity ty in
       let te = M.insert_lvl_metas te in
       let ty = M.insert_lvl_metas ty in       
       T.pp_term Format.std_formatter te;
       Format.printf "@.";       
       T.pp_term Format.std_formatter ty;
       Format.printf "@.";       
       

       M.dkcheck_metavar ();       
       let _ = C.Typing.checking sg te ty in
       List.iter (fun x -> Printf.printf "%s " (U.string_of_cstr x)) !U.cstr_eq;
       let subst = match U.solve_cstr () with
         | None -> raise No_solution
         | Some subst -> subst in
       let te, _ = D.apply_subst_to_term subst te in
       let ty, ty_fv = D.apply_subst_to_term subst ty in
       let ty = mk_ty_univ_poly ty ty_fv in
       let te = mk_term_univ_poly te ty_fv in
       let new_entry = Def (l, id, sc, opq, Some ty, te) in
       up_def_arity := (B.string_of_mident (Env.get_name env), B.string_of_ident id, List.length ty_fv)
                       :: !up_def_arity;
       (* TODO: if a symbol is not opaque the we also need to add a rewriting rule *)       
       S.add_declaration sg l id sc (S.Definable T.Free) ty;
       Format.fprintf out_fmt "%a@." Api.Pp.Default.print_entry new_entry       
            
         
       
       
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
       let ty = replace_arity ty in      
       let ty = M.insert_lvl_metas ty in
       M.dkcheck_metavar ();
       T.pp_term Format.std_formatter ty;
(*       let _ = try let _ = C.Typing.inference sg ty in () with s -> let (_, _, s) = Api.Errors.string_of_exception (fun x -> x) B.dloc s in
                                                      Printf.printf "error was %s\n" s in*)
       let _ = C.Typing.inference sg ty in
       let subst = match U.solve_cstr () with
         | None -> raise No_solution
         | Some subst -> subst in
       let ty, ty_fv = D.apply_subst_to_term subst ty in
(*       T.pp_term Format.std_formatter ty;
       Format.printf "@.";*)
       let ty = mk_ty_univ_poly ty ty_fv in
       (*       let ty = C.RE.snf sg ty in*)
(*       Format.printf "The term is = ";       
       T.pp_term Format.std_formatter ty;
       Format.printf "@.";       
       List.iter (Printf.printf "%s ") ty_fv;*)
       let new_entry = Decl (l, id, sc, opq, ty) in
       up_def_arity := (B.string_of_mident (Env.get_name env), B.string_of_ident id, List.length ty_fv)
                       :: !up_def_arity;
       S.add_declaration sg l id sc opq ty;
       Format.fprintf out_fmt "%a@." Api.Pp.Default.print_entry new_entry

       
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
  | _ -> ()
