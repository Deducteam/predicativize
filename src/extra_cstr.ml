module B = Kernel.Basic
module R = Kernel.Rule
module P = Parsers.Parser         
module D = Lvldk

exception Not_a_lvl

let extra_cstr = ref (fun _ -> [])
        
let read_extra_cstr s =
  Format.printf "Reading extra cstr@.";
  let entries = P.(parse (input_from_file s)) in
  let read_extra_cstr' extra_cstr md_name id_name e =
    let open Parsers.Entry in
    match e with
    | Decl(_, id, _, Definable _, _) -> 
       extra_cstr, B.string_of_ident id, id_name
    | Decl(_, id, _, Static, _) -> 
       extra_cstr, md_name, B.string_of_ident id
    | Rules(_, [r]) ->
       let lhs = R.pattern_to_term r.pat in
       let rhs = r.rhs in 
       begin
       match D.extract_lvl None lhs, D.extract_lvl None rhs with
       | Some t1, Some t2 -> (fun x -> if x = (md_name, id_name)
                                      then (t1, t2) :: (extra_cstr (md_name, id_name))
                                      else (extra_cstr x)), md_name, id_name
       | _, _ -> raise Not_a_lvl end
    | _ -> extra_cstr, md_name, id_name
  in
  let extra_cstr', _, _ = List.fold_left (fun (cstr, md, id) x -> read_extra_cstr' cstr md id x) ((fun _ -> []), "", "") entries in
  extra_cstr := extra_cstr'


       
       
