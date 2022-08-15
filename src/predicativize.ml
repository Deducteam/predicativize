module T = Kernel.Term
module B = Kernel.Basic
module Env = Api.Env
module P = Parsers.Parser
module E = Entry         
module Files = Api.Files
module M = Api.Meta
module A = Agda
open Common

exception Error   
         
(*let sttfa_to_pts inputfile entries =
  let env = Env.init (Parsers.Parser.input_from_file inputfile) in  
  let cfg = M.default_config () in
  let meta_rules = M.parse_meta_files ["metas/sttfa_to_pts.dk"] in
  M.add_rules cfg meta_rules;
  List.map (M.mk_entry cfg env) entries*)

let apply_meta meta inputfile entries =
  try
    let env = Env.init (Parsers.Parser.input_from_file inputfile) in  
    let cfg = M.default_config () in
    let meta_rules = M.parse_meta_files [meta] in
    M.add_rules cfg meta_rules;
    List.map (M.mk_entry cfg env) entries
  with e -> begin
      let _, _, s = Api.Errors.string_of_exception ~red:(fun x -> x) (B.dloc) e in
      Format.printf "%s%s@." (red "ERROR : ")  s;
      raise Error end
  
exception Exit_p
        
let predicativize meta agda_mode agda_with_typecheck_mode inputfile =
  Files.add_path "out";

  let entries = P.(parse (input_from_file inputfile)) in

  (*  let entries = if sttfa_mode then sttfa_to_pts inputfile entries else entries in*)
  let entries =
    match meta with
    | None -> entries
    | Some meta -> apply_meta meta inputfile entries in

  let env = Env.init (Parsers.Parser.input_from_file inputfile) in
  Env.errors_in_snf := true;
  
  let name = Filename.(chop_suffix (basename inputfile) ".dk") in

  let output_file = open_out ("out/" ^ name ^ ".dk") in
  let out_fmt = Format.formatter_of_out_channel output_file in
  
  let ok_entries = ref 0 in
  let ko_entries = ref 0 in  

  let no_errors = ref true in
  
  let new_entries =
    List.map
      (fun e ->
        try
          match E.predicativize_entry env false out_fmt e with
          | None -> None
          | Some x -> ok_entries := 1 + !ok_entries; Some x
        with e -> begin
            let _, _, s = Api.Errors.string_of_exception ~red:(fun x -> x) (B.dloc) e in
            Format.printf "%s%s@." (red "ERROR : ")  s;
            ko_entries := 1 + !ko_entries; no_errors := false; None end)
      entries in

  let new_entries = List.rev @@ opt_list_to_list new_entries in

  Format.printf "%s : %s OK / %s KO@."
    (violet @@ "Finished processing " ^ name)
    (string_of_int !ok_entries)
    (string_of_int !ko_entries);

  if agda_mode || agda_with_typecheck_mode then
    begin
      let name = sanitize name in
      let agda_output_file = open_out ("agda_out/" ^ name ^ ".agda") in
      let agda_out_fmt = Format.formatter_of_out_channel agda_output_file in
      A.pp_file agda_out_fmt @@ Agda.dkfile_to_file name new_entries;
      close_out agda_output_file;
      if agda_with_typecheck_mode then begin
          Format.printf "%s@." (violet "Typechecking with Agda");
          (if Sys.file_exists @@ "agda_out/" ^ name ^ ".agdai" then
             let _ = Sys.command @@ "rm agda_out/" ^ name ^ ".agdai" in ());
          let status = Sys.command @@ "agda -i agda_out/ " ^ "agda_out/" ^ name ^ ".agda" in
          if status = 0
          then Format.printf "%s@." (green "Typecheck successful")
          else Format.printf "%s : return code %d@." (red "ERROR") status end
    end;
  close_out output_file;
  !no_errors
  
let input_files = ref []  
  
let _ =
  let agda_mode = ref false in
  let agda_with_typecheck_mode = ref false in  
  let eta_mode = ref false in
  let extra_cstrs_file = ref None in
  let add_to_path = ref None in
  let meta_file = ref None in  
  dkcheck "theory/pts.dk";
  dkcheck "theory/sttfa.dk";
  (try ignore (Unix.stat "out") with _ -> Unix.mkdir "out" 0o755);
  (try ignore (Unix.stat "agda_out") with _ -> Unix.mkdir "agda_out" 0o755);    
  let options =
    Arg.align
      [
(*        ( "-s", Arg.Unit (fun () -> sttfa_to_pts_mode := true),
          " Handles files in the sttfa syntax, else it expects files in the pts syntax (see theory/pts.dk)") ;
        ( "-o", Arg.Unit (fun () -> optim_enabled := true),
          " Enables optmizations to make the result depend on less universe variables (might render the level constraints unsolvable)") ;*)
        ( "-a", Arg.Unit (fun () -> agda_mode := true),
          " Automatically translates the output to agda files") ;
        ( "-at", Arg.Unit (fun () -> agda_with_typecheck_mode := true),
          " Automatically translates the output to agda files and typechecks them") ;        
        ( "--eta", Arg.Unit (fun () -> eta_mode := true),
          " Uses eta equality") ;        
        ( "--cstr", Arg.String (fun s -> extra_cstrs_file := Some s),
          " A file containing extra constraints to be taken into account") ;
        ( "--meta", Arg.String (fun s -> meta_file := Some s),
          " A file containing metarules to be applied to the files") ; 
        ( "--path", Arg.String (fun s -> add_to_path := match !add_to_path with
                                                        | None -> Some [s]
                                                        | Some l -> Some (s :: l)),
          " Paths to look for .dko files") ;        
      ]
  in
  let usage = "A tool for making definitions predicative\nUsage: " ^ Sys.argv.(0) ^ " [OPTION]... [FILE]...\nAvailable options:" in
  Arg.parse options (fun s -> input_files := s :: !input_files) usage;

  (if !eta_mode = true then Kernel.Reduction.eta := true);
  begin match !add_to_path with
  | None -> ()
  | Some l -> List.iter Files.add_path l end;
  
  let files_with_problems = ref 0 in

  begin match !extra_cstrs_file with
  | Some s -> Extra_cstr.read_extra_cstr s
  | None -> () end;
  
  List.iter
    (fun s ->
      let error_in_file = predicativize !meta_file !agda_mode !agda_with_typecheck_mode s in
      if not error_in_file then files_with_problems := 1 + !files_with_problems else ();
      dkcheck @@ "out/" ^ (Filename.basename s))
    (List.rev !input_files);
  if !files_with_problems = 0
  then Format.printf "%s@." (green "All files were translated without problems")
  else Format.printf "%s@."
         (yellow @@ Format.sprintf
                      "%d of the files had problems and where partially translated"
                      !files_with_problems)
    
    

