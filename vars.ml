module T = Kernel.Term
module B = Kernel.Basic
module Env = Api.Env

let md_univ = ref (B.mk_mident "")           
let counter = ref 0

let reset () =
  var_cnt := 0;
  var_map := []

let fresh () =
  let id = B.mk_ident ("?" ^ (string_of_int !counter)) in
  let name = B.mk_name !md_univ id in
  counter := 1 + !counter;
  T.mk_Const (B.dloc) name

let uvar () = B.mk_name !md_theory (B.mk_ident "var")
                  
let insert_lvl_metas t =
  let open T in  
  match t with
  | Const (_, name) when B.name_eq name (uvar()) ->
     fresh ()
  | App (f,a1,al) -> 
     mk_App (insert_lvl_metas f) (insert_lvl_metas a1) (List.map insert_lvl_metas al)
  | Lam (l,id,t,body) ->
     mk_Lam l id (Option.map insert_lvl_metas t) (insert_lvl_metas body)
  | Pi (l,id,a,b) ->
     mk_Pi l id (insert_lvl_metas a) (insert_lvl_metas b)
  | Kind | Type _ | DB _ | Const _ -> t

