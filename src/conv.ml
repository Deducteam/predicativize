module T = Kernel.Term
module U = Unif
module D = Lvldk

module MakeRE (Conv : Kernel.Reduction.ConvChecker) : Kernel.Reduction.S =
struct

  module rec R : Kernel.Reduction.S =
    Kernel.Reduction.Make (Conv) (Kernel.Matching.Make (R))

  module Rule = Kernel.Rule
  include R

  let univ_conversion sg l r =
    if T.term_eq l r then 
      true
    else match (D.extract_lvl (Some (whnf sg)) l, D.extract_lvl (Some (whnf sg)) r) with
         | Some l', Some r' -> U.cstr_eq := (l',r') :: !U.cstr_eq; true
         | _ -> false

  let rec are_convertible_lst sg : (T.term * T.term) list -> bool = function
  | [] -> true
  | (l, r) :: lst ->
    if T.term_eq l r then are_convertible_lst sg lst
    else begin
        (*    Format.printf "%a = %a -->" T.pp_term l T.pp_term r;      *)
        let l', r' = (whnf sg l, whnf sg r) in
    (*        Format.printf " %a = %a@." T.pp_term l' T.pp_term r';*)
      if univ_conversion sg l' r' then are_convertible_lst sg lst
      else are_convertible_lst sg (R.conversion_step sg (l', r') lst) end

  let are_convertible sg t1 t2 =
    try are_convertible_lst sg [(t1, t2)]
    with Kernel.Reduction.Not_convertible -> false

  let constraint_convertibility _cstr _ _ t1 t2 =
  if T.term_eq t1 t2 then true
  else failwith "Unexpected"
end

module rec RE : Kernel.Reduction.S = MakeRE (RE)

module Typing = Kernel.Typing.Make (RE)
