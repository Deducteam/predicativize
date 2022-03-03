
type alevel = S of int * string
type level = M of int * alevel list 
(* a level in cannonical form is of the form
   M n [S n1 x1; ...; S mk xk] 
   with n >= ni for all i *)

let string_of_lvl (M(n,l_at)) =
  "M (" ^ (string_of_int n) ^ ", [" ^
    (List.fold_left
       (fun acc (S(n, v)) ->
         acc ^ "S(" ^ (string_of_int n) ^ ", " ^ v ^ "), ")
       "" l_at) ^ "])"

(* This type represents the possible ways a variable can occur 
   in a level. We distinguish positive occurence, when x occurs
   in a subterm of the form S n x with n > 0, from zero occurence,
   when x occurs in a term of the form S 0 x. *)
type occurence = No_occ | Pos_occ | Zero_occ

(* [get_occ var t] gives how [var] occurs in [t]. *)                                  
let get_occ var (M(_, at_l)) =
  List.fold_left
    (fun acc (S (m, var2)) ->
      if var = var2 then
        if m > 0 then Pos_occ else Zero_occ
      else acc)
    No_occ at_l

(* [insert_in_at_l t at_l] inserts the atomic level [t] in the list of
   atomic levels [at_l], which is supposed to be ordered. The result is
   also ordered and each variable occurs only one time. *)
let rec insert_in_at_l (S(m,var) as t) at_l =
  match at_l with
  | [] -> [t]
  | S(n,v) :: at_l ->
     if v = var
     then S(max n m, var) :: at_l
     else if v > var then
       t :: (S(n,v)) :: at_l
     else S(n, v) :: (insert_in_at_l t at_l)

(* [nf_of_lvl t] puts [t] in cannonical form *)    
let nf_of_lvl (M(n,l_at)) =
  List.fold_left
    (fun (M(acc_n, acc_l)) (S(n,v)) -> M(max acc_n n, insert_in_at_l (S(n,v)) acc_l))
    (M(n, []))
    l_at

let apply_subst subst (M(n, at_l)) =
  let map_plus n = List.map (fun (S(m, var)) -> S(n + m, var)) in
  let new_at_l, new_n =
    List.fold_left
      (fun (l, n) (S(m,var)) ->
        match subst var with
        | None -> S(m,var) :: l, n
        | Some (M(m',at_l')) -> (map_plus m at_l') @ l, max n (m + m'))
      ([],n)
      at_l
  in nf_of_lvl (M(new_n, new_at_l))

(* [get_min t] gets the minimum n st there is a subterm 
   of the form S n x in t. *)
let get_min (M(n,at_l)) =
  let min_at_l =
    List.fold_left
      (fun acc (S(m,_)) ->
        match acc with
        | None -> Some m
        | Some min -> if m < min
                      then Some m
                      else Some min)
      None
      at_l in
  match min_at_l with
  | None -> n
  | Some x -> x
       
(* [get_fv t] returns the free variables of [t]. *)
let get_fv (M(_,at_l)) =
  List.fold_left (fun acc (S(_,var)) -> var :: acc) [] at_l
