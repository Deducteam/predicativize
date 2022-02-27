module T = Kernel.Term
module B = Kernel.Basic
module Env = Api.Env
module D = Lvldk          
           
let counter = ref 0

let metavar_oc : out_channel option ref = ref None
            
let uvar_name = "var"
               
let open_metavar_oc_and_reset_counter () =
  counter := 0;
  metavar_oc := Some (open_out "metavar.dk")

exception Metavar_oc_not_set
        
let close_metavar_oc () =
  match !metavar_oc with
    | Some x -> close_out x; metavar_oc := None
    | None -> raise Metavar_oc_not_set
  
let add_metavar_to_file id =
  let fmt = match !metavar_oc with
    | Some x -> Format.formatter_of_out_channel x
    | None -> raise Metavar_oc_not_set in
  Format.fprintf fmt "%a@." Api.Pp.Default.print_entry
    (Parsers.Entry.Decl
       ( B.dloc,
         id,
         Kernel.Signature.Public,
         Kernel.Signature.Definable T.Free,
         D.sort_ty))

let dkcheck_metavar () =
  let open Api in
  let open Processor in
  let hook_after env exn =
    match exn with
    | None              -> Env.export env
    | Some (env, lc, e) -> Env.fail_env_error env lc e
  in
  let hook =
    {before = (fun _ -> ()); after = hook_after}
  in
  Processor.handle_files ["metavar.dk"] ~hook TypeChecker

let fresh () =
  let id = B.mk_ident ("?" ^ (string_of_int !counter)) in
  let name = B.mk_name (B.mk_mident "metavar") id in
  add_metavar_to_file id;
  counter := 1 + !counter;
  let cons = T.mk_Const (B.dloc) name in
  T.mk_App D.pts_m D.pts_0_n [T.mk_App D.pts_s D.pts_0_n [cons]]
                  
let rec insert_lvl_metas t =
  let open T in  
  match t with
  | Const (_, name) when (B.string_of_ident (B.id name) = uvar_name) ->
     fresh ()
  | App (f,a1,al) -> 
     mk_App (insert_lvl_metas f) (insert_lvl_metas a1) (List.map insert_lvl_metas al)
  | Lam (l,id,t,body) ->
     mk_Lam l id (Option.map insert_lvl_metas t) (insert_lvl_metas body)
  | Pi (l,id,a,b) ->
     mk_Pi l id (insert_lvl_metas a) (insert_lvl_metas b)
  | Kind | Type _ | DB _ | Const _ -> t
