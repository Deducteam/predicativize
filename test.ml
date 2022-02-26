open Format

type atomic_l = S of int * string
type level = M of int * atomic_l list
(* a level in cannonical form is of the form
   M n [S n1 x1; ...; S mk xk] 
   with n >= ni for all i *)




let string_of_lvl (M(n,l_at)) =
  "M (" ^ (string_of_int n) ^ ", [" ^
    (List.fold_left
       (fun acc (S(n, v)) ->
         acc ^ "S(" ^ (string_of_int n) ^ ", " ^ v ^ "), ")
       "" l_at) ^ "])"
  
type cstr = Eq of level * level | Deq of level * level

let string_of_cstr c =
  match c with
  | Eq(t1,t2) -> (string_of_lvl t1) ^ " = " ^ (string_of_lvl t2)
  | Deq(t1,t2) -> (string_of_lvl t1) ^ " =d " ^ (string_of_lvl t2)               
                                       
                                       
type occurence = No_occ | Pos_occ | Zero_occ

let rec get_occ var (M(_, at_l)) =
  List.fold_left
    (fun acc (S (m, var2)) ->
      if var = var2 then
        if m > 0 then Pos_occ else Zero_occ
      else acc)
    No_occ at_l

type subst = string -> level

let map_plus n = List.map (fun (S(m, var)) -> S(n + m, var))

let rec insert_in_at_l (S(m,var) as t) at_l =
  match at_l with
  | [] -> [t]
  | S(n,v) :: at_l ->
     if v = var
     then S(max n m, var) :: at_l
     else if v > var then
       t :: (S(n,v)) :: at_l
     else S(n, v) :: (insert_in_at_l t at_l)

let nf_of_lvl (M(n,l_at)) =
  List.fold_left
    (fun (M(acc_n, acc_l)) (S(n,v)) -> M(max acc_n n, insert_in_at_l (S(n,v)) acc_l))
    (M(n, []))
    l_at

let nf_of_cstr c =
  match c with
  | Eq(t1, t2) -> Eq(nf_of_lvl t1, nf_of_lvl t2)
  | Deq(t1, t2) -> Deq(nf_of_lvl t1, nf_of_lvl t2)                
    
           
let rec apply_subst subst (M(n, at_l)) =
  let new_at_l =
    List.fold_left
      (fun l (S(m,var)) ->
        match subst var with
        | None -> S(m,var) :: l
        | Some (M(n',at_l')) -> (map_plus m at_l') @ l)
      []
      at_l
  in nf_of_lvl (M(n, new_at_l))

let rec apply_subst_to_cstr subst s =
  match s with
  | [] -> []
  | Eq(t1,t2) :: s ->
     Eq(apply_subst subst t1, apply_subst subst t2) :: (apply_subst_to_cstr subst s)
  | Deq(t1,t2) :: s ->
     Deq(apply_subst subst t1, apply_subst subst t2) :: (apply_subst_to_cstr subst s)

  
(* gets the largest m st that we can write t as S m t' *)
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

(* minimization means that M(1, [S 1 x]) = M(2, [S 2 y, S 1 w])
   is transformed into M(0, [S 0 x]) = M(1, [S 1 y, S 0 w]) *)            
let rec minimize c =
  match c with
  | Eq((M(n1,at1) as t1), (M(n2,at2) as t2))
    | Deq((M(n1,at1) as t1), (M(n2,at2) as t2)) ->
     let k1 = get_min t1 in
     let k2 = get_min t2 in
     if k1 != 0 && k2 != 0 then
       let k = min k1 k2 in
       let t1 = M(n1 - k, List.map (fun (S(n,var)) -> S(n-k,var)) at1) in
       let t2 = M(n2 - k, List.map (fun (S(n,var)) -> S(n-k,var)) at2) in
       match c with
       | Eq (_,_) -> Eq(t1,t2)
       | Deq (_,_) -> Deq(t1,t2)
     else c

let minimize_cstr s = List.map minimize s

let reset_delay s =
  List.map
    (fun c ->
      match c with
      | Eq(t1,t2) -> c
      | Deq(t1,t2) -> Eq(t1,t2))
  s


exception Test  

(* precondition: the constraints must already be minimized *)        
let rec unify subst s =
  match s with
  | [] -> Some subst
  | c :: s ->
     printf "%s@." (string_of_cstr c);     
     match c with

     | Eq (t1, t2) when t1 = t2 -> unify subst s

     | Eq (M (0, [S (0, x)]), t) | Eq (t, M (0, [S(0, x)])) ->
        (* we check if x occurs in t, and how *)        
        begin match get_occ x t with
        (* positive occurence, thus there is no solution *)
        | Pos_occ -> None
        (* zero occurence, thus there is still hope but we still cannot infer
           a substitution from this constraint, thus we delay it *)
        | Zero_occ -> unify subst (s @ [Deq (M (0, [S (0, x)]), t)])
        (* no occurence, thus we can infer a substitution *)
        | No_occ ->
           let new_subst var =
             if var = x then Some t
             (* we also need to apply the new substitution to the image of the old one *)
             else Option.map (apply_subst (fun v -> if v = x then Some t else None)) (subst var) in
           let new_s = minimize_cstr (reset_delay (apply_subst_to_cstr new_subst s)) in
           unify new_subst new_s end

     | Eq (M (0, []), M(n, l)) | Eq (M(n, l), M (0, [])) ->
        if n != 0 then None
        else
          let s' = List.map (fun (S(_, x)) -> Eq (M(0, []), M(0, [S(0,x)]))) l in
          unify subst (s' @ s)

     | Eq(t1, t2) -> unify subst (s @ [Deq(t1,t2)])

     | _ -> raise Test

