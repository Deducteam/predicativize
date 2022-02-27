module T = Kernel.Term
module B = Kernel.Basic
module Env = Api.Env
module P = Parsers.Parser
module E = Entry         
module Files = Api.Files
             
let predicativize input_file =
  Files.add_path "theory";  
  let env = Env.init (P.input_from_file input_file) in
  let entries = P.(parse (input_from_file input_file)) in

  let name = Filename.(chop_suffix (basename input_file) ".dk") in
  let output_file = open_out (name ^ "__out.dk") in
  let out_fmt = Format.formatter_of_out_channel output_file in
  List.iter (E.predicativize_entry env out_fmt) entries;
  close_out

let _ = predicativize "test.dk"
  
(*let input_file = ref "test.dk"               
let _ =
  (* Add theory to file paths *)
  (*  Files.add_path "theory";*)
  Arg.parse [] (fun s -> input_file := s) "";
  let env = Env.init (P.input_from_file !input_file) in
  Vars.md_univ := (P.md_of_input (Env.get_input env));
  let output_file = open_out "final.dk" in
  let out_fmt = Format.formatter_of_out_channel output_file in
  let in_fmt = Format.std_formatter in
  (*  predicativize env in_fmt out_fmt entries;*)
  close_out output_file
 
   
let _ = Files.add_path "theory"
let input_file = ref "test.dk"         
let env = Env.init (P.input_from_file !input_file)

let _ = Metavars.open_metavar_oc_and_reset_counter ()
  
let entries = Parser.(parse (input_from_file !input_file))
let te = match entries with | Decl(l,id,sc,opq,ty)::_ -> ty;;
let te' = Metavars.insert_lvl_metas te
let _ = dkcheck_metavar ()        
let sg = Api.Env.get_signature env

 *)
