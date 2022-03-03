module T = Kernel.Term
module B = Kernel.Basic
module Env = Api.Env
module P = Parsers.Parser
module E = Entry         
module Files = Api.Files
module M = Api.Meta

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

let colored n s =
  "\027[3" ^ string_of_int n ^ "m" ^ s ^ "\027[m"

let green = colored 2

let blue = colored 6

let red = colored 1

exception Exit_p
        
let predicativize optim sttfa_mode inputfile =
  Files.add_path "theory";
  Files.add_path "out";  

  let entries = P.(parse (input_from_file inputfile)) in

  let entries = if sttfa_mode then sttfa_to_pts inputfile entries else entries in

  let env = Env.init (Parsers.Parser.input_from_file inputfile) in
  
  let name = Filename.(chop_suffix (basename inputfile) ".dk") in
  (*  let optim = if name = "leibniz" then false else optim in*)
  let output_file = open_out ("out/" ^ name ^ ".dk") in
  let out_fmt = Format.formatter_of_out_channel output_file in

  try
    List.iter (E.predicativize_entry env optim out_fmt) entries; flush output_file   
  with | e -> begin
             let _, _, s = Api.Errors.string_of_exception ~red:(fun x -> x) (B.dloc) e in
             Printf.printf "%s%s" (red "ERROR : ") s; raise Exit_p end

  
let input_files = ref []  
  
let _ =
  let optim_enabled = ref false in
  let sttfa_to_pts_mode = ref false in
  dkcheck "theory/pts.dk";
  dkcheck "theory/sttfa.dk";
  (try ignore (Unix.stat "out") with _ -> Unix.mkdir "out" 0o755);  
  let options =
    Arg.align
      [
        ( "-s", Arg.Unit (fun () -> sttfa_to_pts_mode := true),
          " Automatically translates sttfa files to the pts encoding") ;
        ( "-o", Arg.Unit (fun () -> optim_enabled := true),
          " Enables optmizations to make the result depend on less universe variables (might render the level constraints unsolvable)")        
      ]
  in
  let usage = "A tool for making definitions predicative\nUsage: " ^ Sys.argv.(0) ^ " [OPTION]... [FILE]...\nAvailable options:" in
  Arg.parse options (fun s -> input_files := s :: !input_files) usage;
  List.iter
    (fun s ->
      predicativize !optim_enabled !sttfa_to_pts_mode s;
      dkcheck @@ "out/" ^ (Filename.basename s))
    (List.rev !input_files)

