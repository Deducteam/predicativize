open Lvl

type cstr = level * level

let cstr_eq : cstr list ref = ref []
let reset_cstr () = cstr_eq := []
                                       
let string_of_cstr (t1, t2) = (string_of_lvl t1) ^ " = " ^ (string_of_lvl t2)
                                       
let nf_of_cstr (t1, t2) = (nf_of_lvl t1, nf_of_lvl t2)

(* [minimize t1 t2] will put the cstr in a form where the exponents of the S 
   are minimal. For instance, M(1, [S(1, x)]) = M(2, [S(1, y), S(2, z)]) is
   transformed into M(0, [S(0, x)]) = M(1, [S(0, y), S(1, z)]). *)
let minimize ((M(n1,at1) as t1), (M(n2,at2) as t2)) =
  let k1 = get_min t1 in
  let k2 = get_min t2 in
  if k1 != 0 && k2 != 0 then
    let k = min k1 k2 in
    let t1 = M(n1 - k, List.map (fun (S(n,var)) -> S(n-k,var)) at1) in
    let t2 = M(n2 - k, List.map (fun (S(n,var)) -> S(n-k,var)) at2) in
    (t1, t2)
  else (t1, t2)

(* Raised when the set of cstr does not a allow for the inferance of a 
   most general solution *)
exception Cannot_infer_sol

(* [unify subst s delayed_s] will try to infer a solution from the constraints [s]
   and the delayed constraints [delayed_s], and build little the little the 
   substitution [subst]. *)
let rec unify subst s delayed_s =
  match s with
  (* If there are no more constraints, but still delayed constraints, then we cannot
     infer a most general solution. *)
  | [] -> if delayed_s = [] then Some subst else raise Cannot_infer_sol
  | (t1, t2) :: s ->
     (* We delay the application of the substitution to the constraint to the moment
        we need to consider it, which makes the algorithm much more efficient. Moreover,
        substitution must always be followed by minimization. *)
     let c = minimize (apply_subst subst t1, apply_subst subst t2) in     
     match c with

     | (t1, t2) when t1 = t2 -> unify subst s delayed_s

     | (M (0, [S (0, x)]), t) | (t, M (0, [S(0, x)])) ->
        (* we check if x occurs in t, and how *)        
        begin match get_occ x t with
        (* positive occurence, thus there is no solution *)
        | Pos_occ -> None
        (* zero occurence, thus there is still hope but now we cannot infer
           a substitution from this constraint, thus we delay it *)
        | Zero_occ -> unify subst s ((M (0, [S (0, x)]), t) :: delayed_s)
        (* no occurence, thus we can infer a substitution *)
        | No_occ ->
           let new_subst var =
             if var = x then Some t
             (* we also need to apply the new substitution to the image of the old one *)
             else Option.map (apply_subst (fun v -> if v = x then Some t else None)) (subst var) in
           unify new_subst (s @ delayed_s) [] end

     | (M (0, []), M(n, l)) | (M(n, l), M (0, [])) ->
        if n != 0 then None
        else
          let s' = List.map (fun (S(_, x)) -> (M(0, []), M(0, [S(0,x)]))) l in
          unify subst (s' @ s) delayed_s

     | (t1, t2) -> unify subst s ((t1,t2) :: delayed_s)
          
let solve_cstr () =
  let new_cstr = List.map (fun c -> minimize (nf_of_cstr c)) !cstr_eq in
  cstr_eq := [];
  unify (fun _ -> None) new_cstr []              
