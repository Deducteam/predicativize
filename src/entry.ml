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

     (*       Format.printf "%a@." T.pp_term ty;
       Format.printf "%a@." T.pp_term te;       *)
     
     U.cstr_eq := !Extra_cstr.extra_cstr (md_name, id_name);
     
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
     let ty = EA.mk_ty_univ_poly ty ty_fv in
     let te = EA.mk_term_univ_poly te ty_fv in

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

     (*       Format.printf "%a@." T.pp_term ty;*)

     U.cstr_eq := !Extra_cstr.extra_cstr (md_name, id_name);
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
     
     let ty = EA.mk_ty_univ_poly ty ty_fv in

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
