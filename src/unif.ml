open Lvl
open Common

type cstr = level * level

let cstr_eq : cstr list ref = ref []
                                       
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
  
(* [simplify t1 t2] removes subterms of the form S n x from [t1] (or [t2]) such that S m x appears 
 in [t2] (or [t1]) with n < m. By doing this, we simplify the constraints while preserving the 
 set of solutions. *)
let simplify ((M(n1,at1)), (M(n2,at2))) =
  let rec aux l1 l2 acc1 acc2 =
    match l1, l2 with
    | (S(n1,v1) as t1) :: l1', (S(n2,v2) as t2) :: l2' ->
       if v1 > v2      then aux l1  l2' acc1         (t2 :: acc2)
       else if v2 > v1 then aux l1' l2  (t1 :: acc1) acc2
       else if n1 = n2 then aux l1' l2' (t1 :: acc1) (t2 :: acc2)
       else if n1 > n2 then aux l1' l2' (t1 :: acc1) acc2
       else                 aux l1' l2' acc1         (t2 :: acc2)
    | [], _ | _, [] -> (List.rev acc1) @ l1, (List.rev acc2) @ l2
  in let at1, at2 = aux at1 at2 [] [] in
     M(n1,at1), M(n2,at2)
        
let fresh_var = ref 0
let fresh_var2 = ref 0
  
(* [unify subst s delayed_s] will try to infer a solution from the constraints [s]
   and the delayed constraints [delayed_s], and build little the little the 
   substitution [subst]. *)
let rec unify subst s delayed_s =
  match s with
  (* If there are no more constraints, but still delayed constraints, then we cannot
     infer a most general solution. *)
  | [] -> if delayed_s = []
          then Some subst
          else
            begin
              Format.printf "%s " (yellow "Cannot infer solution");
              apply_heuristic subst delayed_s
            end 
  | (t1, t2) :: s ->
     (* We delay the application of the substitution to the constraint to the moment
        we need to consider it, which makes the algorithm much more efficient. Moreover,
        substitution must always be followed by simplification and minimization. *)
     let c = minimize @@ simplify (apply_subst subst t1, apply_subst subst t2) in
     match c with

     (* t1 = t2 *)
     | (t1, t2) when t1 = t2 -> unify subst s delayed_s

     (* x = t or t = x*)
     | (M (0, [S (0, x)]), t) | (t, M (0, [S(0, x)])) ->
        (* we check if x occurs in t, and how *)        
        begin match get_occ x t with

        (* no occurence, thus we map x to t *)
        | No_occ ->
           let new_subst var =
             if var = x then Some t
             (* we also need to apply the new substitution to the image of the old one *)
             else Option.map (apply_subst (fun v -> if v = x then Some t else None)) (subst var) in
           unify new_subst (s @ delayed_s) []

        (* zero occurence, we map x to (t \ x) |_| x', with x' fresh *)
        | Zero_occ -> (* unify subst s ((M (0, [S (0, x)]), t) :: delayed_s) *)
           let fresh_x = "??" ^ (string_of_int !fresh_var) in
           fresh_var := 1 + !fresh_var;
           let t = apply_subst (fun v -> if v = x then Some (M(0, [S(0, fresh_x)])) else None) t in
           let new_subst var =
             if var = x then Some t
             (* we also need to apply the new substitution to the image of the old one *)
             else Option.map (apply_subst (fun v -> if v = x then Some t else None)) (subst var) in
           unify new_subst (s @ delayed_s) []

        (* positive occurence, thus there is no solution *)
        | Pos_occ -> Format.printf "No solution to cstr %s@." (string_of_cstr c); None end

     (* 0 = t or t = 0 *)
     | (M (0, []), M(n, l)) | (M(n, l), M (0, [])) ->
        if n != 0 then (Format.printf "No solution to cstr %s@." (string_of_cstr c); None)
        else
          let s' = List.map (fun (S(_, x)) -> (M(0, []), M(0, [S(0,x)]))) l in
          unify subst (s' @ s) delayed_s

     (* any other form of constraint *)
     | (t1, t2) ->
        (* we delay the treatement of this cstr *)
        unify subst s ((t1,t2) :: delayed_s)

(* if we are blocked, we try to apply heuristics which 
   migth make us lose some solutions, but which simplifies constraints *)                 
and apply_heuristic subst delayed_s =

  (* [try_heuristic heuristic] will try [heuristic] with all elements of [delayed_s] until it
   get a Some x, in which case it stops and returns it, else it returns None *)
  let try_heuristic heuristic =
    List.fold_left (fun res x -> if res != None then res else heuristic x) None delayed_s in

  (* this heuristic tries to compute the symmetric difference [new_c] of a constraint [c], 
     and if by doing this we get a new cstr, then we get back to unify, but we replace every
     occurence of [c] in [delayed_s] by [new_c] *)
  let diff ((M(n1,l1), M(n2,l2)) as c) =
    let new_c =
      (M(n1, List.filter (fun x -> not (List.mem x l2)) l1),
       M(n2, List.filter (fun x -> not (List.mem x l1)) l2)) in
    if c = new_c then None
    else
      let new_s = List.map (fun y -> if y = c then new_c else y) delayed_s in
      unify subst new_s [] in
  
  (* if [c] is of the form M n (S m x) = t or t = M n (S m x), then we lift all variables with indices
     smaller then m, so they are at least m, and then we get back to unify with this simplified cstr. 
     we do this transformation so that the minimization step would then give M 0 (S 0 x') for some t' *)
  let lift c = match c with
    | (M (n, [S(m, x)]), M(_, at_l)) | (M(_, at_l), M (n, [S(m, x)])) ->
       let fresh_prefix = fresh_var2 := 1 + !fresh_var2;
                          "?" ^ (string_of_int !fresh_var2) in

       (* for each S k y in at_l with k < n, we send y to S (n - k) y', for some fresh y' *)
       let subst_lift_var =
         List.fold_left
           (fun acc (S(k,v)) ->
             if n > k
             then (fun var -> if var = v then Some (M(n - k,[S(n - k, fresh_prefix ^ v)])) else acc var)
             else acc)
           (fun _ -> None) at_l in

       (* if we have m < n then we send x to S (n - m) x', for some fresh x'. note that if x
           appears also in at_l, because the constraints in delayed_s have already been simplified by
           simplify, then x necesseraly appears in at_l with the exponent m. in this case, we 
           redefine subst x, but it remains with the same value, so this is sound. *)
       let subst_lift_var =
         if n = m
         then subst_lift_var
         else (fun var ->
           if var = x
           then Some (M(n - m,[S(n - m, fresh_prefix ^ x)]))
           else subst_lift_var var) in

       (* finally, we also have to apply the subst_lift_var to the image of subst *)
       let subst var =
         match subst_lift_var var with
         | Some t -> Some t
         | None -> Option.map (apply_subst subst_lift_var) (subst var) in
       
       unify subst delayed_s []
    | _ -> None in

  (* we take the first two elements of the smaller list (of size > 1) and make
     them equal. then we get back to unify and see if this gets us a solution. *)
  let mk_vars_equal (M(_,l1), M(_,l2)) =
    (* we pick the first two elements of the smaller list *)
    let S(m1, x1), S(m2, x2) = 
      if List.length l1 > List.length l2 && List.length l2 > 1
      then (List.nth l2 0, List.nth l2 1)
      else (List.nth l1 0, List.nth l1 1) in
    (* we define x as the smaller one, y as the larger one, and k as the diff between their indices  *)
    let x, y, k = if m1 > m2 then x2, x1, m1 - m2 else x1, x2, m2 - m1 in
    (* we map x to S k y. this way, by applying this subst to the cstr, the two first elements
     of the smaller list now become the same one *)
    let new_subst var =
      if var = x then Some (M(k,[S(k,y)])) else
        (* as always, if x != var, we still need to apply the new subst
         to the image of the old one *)
        Option.map (apply_subst (fun v ->
                        if v = x then Some (M(k,[S(k,y)])) else None)) (subst var) in
    unify new_subst delayed_s [] in

  Format.printf "trying diff, ";
  match try_heuristic diff with
  | Some x -> Some x
  | None -> Format.printf "trying lift, ";
     match try_heuristic lift with
     | Some x -> Some x
     | None -> Format.printf "trying mk_vars_equal, "; try_heuristic mk_vars_equal

(* tries to solve the cstrs in !cstr_eq *)
let solve_cstr () =
  fresh_var := 0;
  let new_cstr = !cstr_eq in
  cstr_eq := [];
  unify (fun _ -> None) new_cstr []
