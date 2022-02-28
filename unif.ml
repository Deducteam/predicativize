open Lvl

type cstr = Eq of level * level | Deq of level * level

let cstr_eq : cstr list ref = ref []
let reset_cstr () = cstr_eq := []
                                       
let string_of_cstr c =
  match c with
  | Eq(t1,t2) -> (string_of_lvl t1) ^ " = " ^ (string_of_lvl t2)
  | Deq(t1,t2) -> (string_of_lvl t1) ^ " =d " ^ (string_of_lvl t2)               
                                       
let nf_of_cstr c =
  match c with
  | Eq(t1, t2) -> Eq(nf_of_lvl t1, nf_of_lvl t2)
  | Deq(t1, t2) -> Deq(nf_of_lvl t1, nf_of_lvl t2)                
    
let rec apply_subst_to_cstr subst s =
  match s with
  | [] -> []
  | Eq(t1,t2) :: s ->
     Eq(apply_subst subst t1, apply_subst subst t2) :: (apply_subst_to_cstr subst s)
  | Deq(t1,t2) :: s ->
     Deq(apply_subst subst t1, apply_subst subst t2) :: (apply_subst_to_cstr subst s)

(* minimization means that M(1, [S 1 x]) = M(2, [S 2 y, S 1 w])
   is transformed into M(0, [S 0 x]) = M(1, [S 1 y, S 0 w]) *)            
let minimize c =
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
      | Eq(_,_) -> c
      | Deq(t1,t2) -> Eq(t1,t2))
  s

exception Test  
        
(* precondition: the constraints must already be minimized *)        
let rec unify subst s =
  match s with
  | [] -> Some subst
  | c :: s ->
     (*     Format.printf "%s@." (string_of_cstr c);     *)
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


let solve_cstr () =
  let new_cstr = List.map (fun c -> minimize (nf_of_cstr c)) !cstr_eq in
  cstr_eq := [];
  let empty_subst _ = None in
  unify empty_subst new_cstr
              
