module T = Kernel.Term
module B = Kernel.Basic
module Env = Api.Env
module P = Parsers.Parser
module E = Entry         
module Files = Api.Files
module M = Api.Meta

let sttfa_to_pts_mode = ref false

let sttfa_to_pts inputfile entries =
  let env = Env.init (Parsers.Parser.input_from_file inputfile) in  
  let cfg = M.default_config () in
  let meta_rules = M.parse_meta_files ["metas/sttfa_to_pts.dk"] in
  M.add_rules cfg meta_rules;
  List.map (M.mk_entry cfg env) entries

let dkcheck file =
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
  Processor.handle_files [file] ~hook TypeChecker

  
let predicativize inputfile =
  Files.add_path "theory";
  Files.add_path "out";  
  Format.printf "ola1@.";  
  let entries = P.(parse (input_from_file inputfile)) in

  let entries = if !sttfa_to_pts_mode then sttfa_to_pts inputfile entries else entries in

  let env = Env.init (Parsers.Parser.input_from_file inputfile) in
  
  let name = Filename.(chop_suffix (basename inputfile) ".dk") in
  let output_file = open_out ("out/" ^ name ^ ".dk") in
  let out_fmt = Format.formatter_of_out_channel output_file in
  try
    List.iter (E.predicativize_entry env out_fmt) entries; flush output_file   
  with | e -> begin
             let _, _, s = Api.Errors.string_of_exception ~red:(fun x -> x) (B.dloc) e in
             Printf.printf "Error : %s" s end;
  Format.printf "ola2@."            
  (*  close_out output_file*)

  
let input_files = ref []  
  
let _ =
  let options =
    Arg.align
      [
        ( "-s", Arg.Unit (fun () -> sttfa_to_pts_mode := true),
          " Automatically translates sttfa files to the pts encoding")
      ]
  in
  let usage = "Usage: " ^ Sys.argv.(0) ^ " [OPTION]... [FILE]...\nAvailable options:" in
  Arg.parse options (fun s -> input_files := s :: !input_files) usage;
  List.iter (fun s -> predicativize s; dkcheck @@ "out/" ^ (Filename.basename s)) (List.rev !input_files)

