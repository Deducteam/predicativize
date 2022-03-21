module Env = Api.Env
module T = Kernel.Term
module B = Kernel.Basic
module A = Agda
module M = Metavars
module C = Conv
module U = Unif
module D = Lvldk
module S = Kernel.Signature
module L = Lvl
module EA = Entry_aux
open Common

exception Not_a_patt
       
let rec term_to_pattern t =
  let open T in
  let open Kernel.Rule in
  match t with
  | App(Const(l, c), t1, tl) -> Pattern(l, c, List.map term_to_pattern (t1 :: tl))
  | App(DB(l, id, n), t1, tl) -> Var(l, id, n, List.map term_to_pattern (t1 :: tl))
  | Lam(l, id, _, body) -> Lambda(l, id, term_to_pattern body)
  | Const(l, c) -> Pattern(l, c, [])
  | DB(l, id, n) -> Var(l, id, n, [])
  | _ -> raise Not_a_patt

exception Impossible
exception Non_atomic_lvl_in_lhs
(*        
(* [linearize lhs rhs] linearizes [lhs]. In the proccess, the db indices change so we also replace
   them with the new ones in [rhs]. Finally, we also return the rule context. *)
let linearize lhs rhs =
  let open T in
  let ctx = ref [] in
  let add_var loc id n depth =
    if n < depth
    then mk_DB loc id n
    else 
      let s_id = B.string_of_ident id in
      let k = List.length !ctx in
      if List.mem s_id !ctx
      then let new_s_id = s_id ^ "_" ^ (string_of_int k) in
           ctx := new_s_id :: !ctx; mk_DB loc (B.mk_ident new_s_id) (k + depth)
      else begin ctx := s_id :: !ctx; mk_DB loc id (k + depth) end in
  (* linearizes the rule and generates the new rule context ctx *)
  let rec mk_lhs depth t =
    match t with
    | App(head, t1, tl) ->
       (* We do it in reverse order so the indices grow from right to left. This is the way the
        indices need to be for dedukti to be happy. *)
       let tl = List.rev @@ List.map (mk_lhs depth) @@ List.rev tl in
       let t1 = mk_lhs depth t1 in
       let head = match head with
         | DB(loc, id, n) -> add_var loc id n depth
         | Const(_, name) when (B.string_of_ident (B.id name) = "M" &&
                                  B.string_of_mident (B.md name) = "pts") ->
            raise Non_atomic_lvl_in_lhs
         | _ -> head in
       mk_App head t1 tl
    | DB(loc, id, n) -> add_var loc id n depth
    | Const(_,_) -> t
    | Lam(l, id, ty_op, body) ->
       let body = mk_lhs (depth + 1) body in
       let ty_op = Option.map (mk_lhs depth) ty_op in
       mk_Lam l id ty_op body
    | _ -> raise Not_a_patt in
  (* updates the db indices according to the new context ctx produced by mk_lhs *)
  let rec mk_rhs depth t =
    match t with
    | App(head, t1, tl) ->
       mk_App (mk_rhs depth head) (mk_rhs depth t1) (List.map (mk_rhs depth) tl)
    | DB(loc, id, n) ->
       if n < depth
       then t
       else begin match pos (B.string_of_ident id) (List.rev !ctx) with
            | Some x -> mk_DB loc id (x + depth)
            | None -> raise Impossible end
    | Lam(loc, id, ty_op, body) ->
       mk_Lam loc id (Option.map (mk_rhs depth) ty_op) (mk_rhs (depth + 1) body)
    | Pi (loc, id, ty, body) ->
       mk_Pi loc id (mk_rhs depth ty) (mk_rhs (depth + 1) body)
    | _ -> t in
  let lhs = mk_lhs 0 lhs in
  let rhs = mk_rhs 0 rhs in
  (lhs, rhs, !ctx)
 *)
(* [transform_rule func lhs rhs] *)
let traverse_and_transform_rule func lhs rhs =
  let open T in
  let ctx = ref [] in
  let rec mk_lhs depth t =
    match t with
    | App(head, t1, tl) ->
       (* We do it in reverse order so the indices grow from right to left. This is the way the
        indices need to be for dedukti to be happy. *)
       let tl = List.rev @@ List.map (mk_lhs depth) @@ List.rev tl in
       let t1 = mk_lhs depth t1 in
       let head = match head with
         | DB(loc, id, n) -> func ctx depth loc id n 
         | Const(_, name) when (B.string_of_ident (B.id name) = "M" &&
                                  B.string_of_mident (B.md name) = "pts") ->
            raise Non_atomic_lvl_in_lhs
         | _ -> head in
       mk_App head t1 tl
    | DB(loc, id, n) -> func ctx depth loc id n
    | Const(_,_) -> t
    | Lam(l, id, ty_op, body) ->
       let body = mk_lhs (depth + 1) body in
       let ty_op = Option.map (mk_lhs depth) ty_op in
       mk_Lam l id ty_op body
    | _ -> raise Not_a_patt in
  (* updates the db indices according to the new context ctx produced by mk_lhs *)
  let rec mk_rhs depth t =
    match t with
    | App(head, t1, tl) ->
       mk_App (mk_rhs depth head) (mk_rhs depth t1) (List.map (mk_rhs depth) tl)
    | DB(loc, id, n) ->
       if n < depth
       then t
       else begin match pos (B.string_of_ident id) (List.rev !ctx) with
            | Some x -> mk_DB loc id (x + depth)
            | None -> raise Impossible end
    | Lam(loc, id, ty_op, body) ->
       mk_Lam loc id (Option.map (mk_rhs depth) ty_op) (mk_rhs (depth + 1) body)
    | Pi (loc, id, ty, body) ->
       mk_Pi loc id (mk_rhs depth ty) (mk_rhs (depth + 1) body)
    | _ -> t in
  let lhs = mk_lhs 0 lhs in
  let rhs = mk_rhs 0 rhs in
  
  (lhs, rhs, !ctx)

let linearize lhs rhs =
  let linearize' ctx depth loc id n =
    if n < depth
    then T.mk_DB loc id n
    else 
      let s_id = B.string_of_ident id in
      let k = List.length !ctx in
      if List.mem s_id !ctx
      then let new_s_id = s_id ^ "_" ^ (string_of_int k) in
           ctx := new_s_id :: !ctx; T.mk_DB loc (B.mk_ident new_s_id) (k + depth)
      else begin ctx := s_id :: !ctx; T.mk_DB loc id (k + depth) end in
  traverse_and_transform_rule linearize' lhs rhs

let get_rule_ctx lhs rhs =
  let get_rule_ctx' ctx depth loc id n =
    let id_s = B.string_of_ident id in
    if n >= depth && not (List.mem id_s !ctx)
    then ctx := id_s :: !ctx;
    let n = match pos id_s (List.rev !ctx) with
      | Some x -> x
      | None -> raise Impossible in
    T.mk_DB loc id (n + depth) in
  traverse_and_transform_rule get_rule_ctx' lhs rhs  

let rec apply_subst_k_times subst k t =
  if k = 0 then t
  else let new_t = Kernel.Exsubst.ExSubst.apply subst 0 t in
       if new_t = t then new_t
       else apply_subst_k_times subst (k - 1) new_t

let rec remove_non_atomic_lvls_in_lhs t =
  let open T in
  match t with
  | App(Const(_, n1), _, [t2]) when (B.string_of_ident (B.id n1) = "M") ->
     begin
       match D.extract_lvl_set None t2 with
       | None -> raise Impossible
       | Some [] -> []
       | Some lvl_set ->
          let t1 = L.M(0, [List.hd lvl_set]) in
          List.map (fun x -> (t1, L.M(0, [x]))) (List.tl lvl_set)
     end
  | App(_, t1, tl) ->
     let c1 = remove_non_atomic_lvls_in_lhs t1 in
     let cl = List.map remove_non_atomic_lvls_in_lhs tl in     
     List.fold_left (fun acc x -> x @ acc) c1 cl
  | DB(_, _, _) -> []
  | Const(_,_) -> []
  | Lam(_, _, ty_op, body) ->
     let body_c = remove_non_atomic_lvls_in_lhs body in
     begin
       match ty_op with
       | None -> body_c
       | Some x -> body_c @ (remove_non_atomic_lvls_in_lhs x)
     end
  | _ -> raise Not_a_patt

exception Cannot_translate_rule  

let predicativize_rule env out_fmt loc (r : Kernel.Rule.partially_typed_rule) =
  let open Parsers.Entry in
  let sg = Api.Env.get_signature env in
  let module Pp = Api.Pp.Make (struct
               let get_name () = Env.get_name env
             end) in
  Format.printf "[ %s ] " (blue "Rewrite rule");
  
  let lhs = Kernel.Rule.pattern_to_term r.pat in
  let lhs = EA.replace_arity lhs in
  let lhs = M.insert_lvl_metas env lhs in
  let lhspt = term_to_pattern lhs in

  let rhs = EA.replace_arity r.rhs in
  let rhs = M.insert_lvl_metas env rhs in

  (* We use the check_rule to try to check that the rule satisfies sr. In the process, constraints 
     are generated to assure that this is indeed the case. Note that infering the type of the lhs 
     and then checking that the rhs has the same type would not work, as we do not know the types
     of the variables in the rule context. I see no clear way of infering them, thus this seems to
     be the only option to me. *)
  (* We disable the unsatisfiable cstrs warnigs that will be produced. The only important thing is
     that we get the cstrs during the proccess. *)
  Kernel.Basic.Debug.disable_flag Kernel.Basic.Debug.d_warn;
  let _ = List.map (C.Typing.check_rule sg) [{name = r.name; ctx = r.ctx; pat = lhspt; rhs = rhs}] in
  Kernel.Basic.Debug.enable_flag Kernel.Basic.Debug.d_warn;
  
  let subst = match U.solve_cstr () with
    | None -> raise Cannot_translate_rule
    | Some subst -> subst in

  let lhs, _ = D.apply_subst_to_term subst lhs in
  let rhs, _ = D.apply_subst_to_term subst rhs in

  (* we use dkmeta to put the lvls in normal form. in particular, we want to reduce in the lhs the 
   M 0 [S 0 x] to just x, so they can match arbitrary levels *)
  let cfg = Api.Meta.default_config () in
  let meta_rules = Api.Meta.parse_meta_files ["metas/compute_lvl_nf.dk"] in
  Api.Meta.add_rules cfg meta_rules;

  let lhs = Api.Meta.mk_term cfg lhs in
  let rhs = Api.Meta.mk_term cfg rhs in

  (* It migth be that the resulting lhs has non atomic levels, such as M 0 [S 0 x, S 0 y]. 
     In this case we need to identify x and y in order for the lhs to only contain lvl vars. 
     Indeed, a rule with a lvl max on the lhs cannot be used to compute constraints
     because M 0 [S 0 x, S 0 y] will never match a lvl metavariable. *)  
  U.cstr_eq := remove_non_atomic_lvls_in_lhs lhs;
  let remove_non_alvl_subst = match U.solve_cstr () with
    | None -> raise Cannot_translate_rule
    | Some subst -> subst in

  let lhs, vars = D.apply_subst_to_term remove_non_alvl_subst lhs in
  let rhs, _ = D.apply_subst_to_term remove_non_alvl_subst rhs in

  let lhs = Api.Meta.mk_term cfg lhs in
  let rhs = Api.Meta.mk_term cfg rhs in

  (* converts the metavariable constants ?0, ?1, ... to variables *)
  let vars = remove_duplicates vars in
  let lhs = EA.cons_to_vars (List.rev vars) (List.length r.ctx) lhs in
  let rhs = EA.cons_to_vars (List.rev vars) (List.length r.ctx) rhs in     

  (* linearizes the rule and generates the appropriate new context *)
  let lhs, rhs, ctx = linearize lhs rhs in

  let lhspt = term_to_pattern lhs in
  let ctx = List.map (fun s -> B.dloc, B.mk_ident s, None) (List.rev ctx) in

  (* we print the result as it is : linear and untyped *)  
  let untyped_linear_entry = Rules(loc, [{name = r.name; ctx = ctx; pat = lhspt; rhs = rhs}]) in
  Format.fprintf out_fmt "%a@." Pp.print_entry untyped_linear_entry;
  let res = Env.add_rules env [{name = r.name; ctx = ctx; pat = lhspt; rhs = rhs}] in
  (* we also recover the typed version of the rule along with the substitution that 
    makes the lhs well typed *)
  let subst, typed_rule = fst (List.hd res), snd (List.hd res) in

  (* from the typable version and the subst, we calculate the version of lhs, rhs 
     that are indeed typable, by applying subst *)
  (* we might need to apply the substitution many times, because the image of the subst
     migth not be in normal form. in any case, the number of vars is an upper bound
     for this, and it is at most the length of ctx *)
  let typable_lhs = apply_subst_k_times subst (List.length ctx) @@
                    Kernel.Rule.pattern_to_term typed_rule.pat in
  let typable_rhs = apply_subst_k_times subst (List.length ctx) @@ typed_rule.rhs in
  
  let typable_lhs, typable_rhs, ctx = get_rule_ctx typable_lhs typable_rhs in

  (* removed unused variables from the ctx with types. this messes up db indices
     but we assume that from this point on we don't need them anymore *)
  let ctx = List.rev @@
              List.fold_left
                (fun acc (loc, id, ty) ->
                  if List.mem (B.string_of_ident id) ctx
                  then (loc, id, Some ty) :: acc else acc) [] typed_rule.ctx in
  
  let typed_non_linear_entry =
    Rules(loc, [{name = typed_rule.name;
                 ctx = ctx;
                 pat = term_to_pattern typable_lhs;
                 rhs = typable_rhs}]) in

  Format.printf "%s@." (green "Ok");
  Some typed_non_linear_entry
