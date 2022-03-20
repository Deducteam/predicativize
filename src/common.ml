let ( let* ) o f =
  match o with
  | None -> None
  | Some x -> f x

(* [pos x l] returns Some n if [x] appears in position n of [l],
   else None. *)                  
let rec pos x l =
  match l with
  | [] -> None
  | y :: l -> if y = x then Some 0
              else Option.map (fun a -> 1 + a) (pos x l)

let colored n s =
  "\027[3" ^ string_of_int n ^ "m" ^ s ^ "\027[m"

let green = colored 2
let yellow = colored 3
let blue = colored 6
let red = colored 1
let violet = colored 5

let remove_duplicates l =
  List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) [] l
                     
let opt_list_to_list l =
  List.fold_left
    (fun acc x ->
      match x with
      | None -> acc
      | Some e -> e :: acc)
    [] l

let all_some_list_to_some_list l =
  List.fold_left
    (fun l x ->
      match x, l with
      | None, _ | _, None -> None
      | Some x, Some l -> Some (x :: l))
    (Some []) l
  
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
    
let sanitize s =
  let s = String.map (fun c -> if c = '_' then '-'
                               else if c = '{' || c = '}' then '|'
                               else if c = '.' then '-'
                               else if c = '(' || c = ')' then '-' else c) s in
(*  let s = if int_of_string_opt @@ String.make 1 @@ String.get s ((String.length s) - 1) = None
          then s else s ^ "|" in*)
  let s = String.map (fun c -> if c = '?' then 'l' else c) s in
  if String.get s 0 = '-' then "X" ^ s else s

