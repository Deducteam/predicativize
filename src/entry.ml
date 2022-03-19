module Env = Api.Env
module T = Kernel.Term
module B = Kernel.Basic
module A = Agda
module M = Metavars
module C = Conv
module U = Unif
module D = Lvldk
module S = Kernel.Signature
module R = Rule
module L = Lvl
module EA = Entry_aux
open Common

exception No_solution                  
exception Def_without_type
        
let predicativize_entry env optim out_fmt e =
  let open Parsers.Entry in
  let sg = Api.Env.get_signature env in

  (* dk terms pretty printer *)
  let module Pp = Api.Pp.Make (struct
               let get_name () = Env.get_name env
             end) in
  M.reset_counter ();

  let cfg = Api.Meta.default_config () in
  let meta_rules = Api.Meta.parse_meta_files ["metas/compute_lvl_nf.dk"] in
  Api.Meta.add_rules cfg meta_rules;

  match e with
  | Def(l, id, sc, opq, ty_op, te) ->
     let md_name = B.string_of_mident (Env.get_name env) in
     let id_name = B.string_of_ident id in
     Format.printf "[ %s.%s ] " (blue md_name) (blue id_name); Format.print_flush ();
     
     let ty = match ty_op with
       | Some x -> x
       | None ->
          let name = B.string_of_ident id in
          Printf.printf "Error : all Defs need to have their type, but %s has no type\n" name;
          raise Def_without_type in

     let te = EA.replace_arity te in
     let ty = EA.replace_arity ty in

     let te = M.insert_lvl_metas env te in
     let ty = M.insert_lvl_metas env ty in 
     
     U.cstr_eq := !Extra_cstr.extra_cstr (md_name, id_name);
     let _ = C.Typing.checking sg te ty in
     
     Format.printf "Solving %n constraints. " (List.length !U.cstr_eq); Format.print_flush ();       
     let subst = match U.solve_cstr () with
       | None -> raise No_solution
       | Some subst -> subst in

     let ty, ty_fv =
       (* if optim = true, we only take as free lvl vars the ones which appears in the
          the argument of a Set in the type *)
       if optim then 
         let new_ty, _ = D.apply_subst_to_term subst ty in
         (new_ty, D.get_vars_in_u subst ty)
       else D.apply_subst_to_term subst ty in

     let te, _ = D.apply_subst_to_term subst te in
     let ty = EA.mk_ty_univ_poly ty ty_fv in
     let te = EA.mk_term_univ_poly te ty_fv in

     (* we use dkmeta to simplify the M 0 (S 0 x) to x. this is not required,
        but makes files more readable*)
     let ty = Api.Meta.mk_term cfg ty in
     let te = Api.Meta.mk_term cfg te in     

     Format.printf "%s@." @@ green @@
       "Solution found with " ^ (string_of_int (List.length ty_fv)) ^ " up vars.";
     
     let new_entry = Def (l, id, sc, opq, Some ty, te) in
     Format.fprintf out_fmt "%a@." Pp.print_entry new_entry;
     EA.up_def_arity :=
       (B.string_of_mident (Env.get_name env), B.string_of_ident id, List.length ty_fv) 
       :: !EA.up_def_arity;
     Env.define env l id sc opq te (Some ty);
     Some new_entry

  | Decl(l, id, sc, opq, ty) ->

     let md_name = B.string_of_mident (Env.get_name env) in
     let id_name = B.string_of_ident id in
     Format.printf "[ %s.%s ] " (blue md_name) (blue id_name); Format.print_flush ();

     let ty = EA.replace_arity ty in
     let ty = M.insert_lvl_metas env ty in

     U.cstr_eq := !Extra_cstr.extra_cstr (md_name, id_name);
     let _ = C.Typing.inference sg ty in

     Format.printf "Solving %n constraints. " (List.length !U.cstr_eq); Format.print_flush ();
     let subst = match U.solve_cstr () with
       | None -> raise No_solution
       | Some subst -> subst in

     let ty, ty_fv =
       (* if optim = true, we only take as free lvl vars the ones which appears in the
          the argument of a Set in the type *)
       if optim then
         let new_ty, _ = D.apply_subst_to_term subst ty in
         (new_ty, D.get_vars_in_u subst ty)
       else D.apply_subst_to_term subst ty in

     Format.printf "%s@." @@ green @@
       "Solution found with " ^ (string_of_int (List.length ty_fv)) ^ " up vars.";
     
     let ty = EA.mk_ty_univ_poly ty ty_fv in

     (* we use dkmeta to simplify the M 0 (S 0 x) to x. this is not required,
        but makes files more readable*)
     let ty = Api.Meta.mk_term cfg ty in
     
     let new_entry = Decl (l, id, sc, opq, ty) in

     Format.fprintf out_fmt "%a@." Pp.print_entry new_entry;       
     EA.up_def_arity :=
       (B.string_of_mident (Env.get_name env), B.string_of_ident id, List.length ty_fv)
       :: !EA.up_def_arity;
     Env.declare env l id sc opq ty;
     Some new_entry

  | Rules(loc, [r]) -> R.predicativize_rule env out_fmt loc r
  | Rules(_, _) -> Format.printf "TODO@."; None
  | _ -> None
