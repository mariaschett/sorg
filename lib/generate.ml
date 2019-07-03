open Core
open Ebso
open Evmenc
open Z3util
open Instruction
open Rule
open Subst

let timeout = ref 0

let is_translation_valid s t =
  let c = enc_trans_val (mk_enc_consts s (`User [])) t in
  match solve_model_timeout [c] !timeout with
    | None -> true
    | Some _ -> false

let equiv = is_translation_valid

let eq_mod_push_arg i i' = match i, i' with
  | PUSH _, PUSH _ -> true
  | _ -> [%eq: Instruction.t] i i'

let rec strip_all r = List.dedup_and_sort ~compare:Rule.compare ([r] @ strip_fst r @ strip_last r @ strip_both r)
and
  strip_fst r = match r.lhs, r.rhs with
  | i1 :: l', i2 :: r' when eq_mod_push_arg i1 i2 ->
    if equiv l' r' then strip_all {lhs = l'; rhs = r'} else []
  | _, _ -> []
and
  strip_last r = match List.rev r.lhs, List.rev r.rhs with
  | j1 :: rl', j2 :: rr' when eq_mod_push_arg j1 j2 ->
    let l' = List.rev rl' and r' = List.rev rr' in
    if equiv l' r' then strip_all {lhs = l'; rhs = r'} else []
  | _, _ -> []
and
  strip_both r = match r.lhs, r.rhs with
  | i1 :: l', i2 :: r' when eq_mod_push_arg i1 i2 ->
    (match List.rev l', List.rev r' with
     | j1 :: rl'', j2 :: rr'' when eq_mod_push_arg j1 j2 ->
       let l'' = List.rev rl'' and r'' = List.rev rr'' in
       if equiv l'' r'' then strip_all {lhs = l''; rhs = r''} else []
     | _, _ -> [])
  | _, _ -> []

let strip r =
  let sr = strip_all r in
  let most_context r = not (List.exists sr ~f:(fun r' ->
      not ([%eq: Rule.t] r r') &&
      is_subrule r' r))
  in
  List.filter sr ~f:most_context

let generalize r =
  let r_0 = maximal_rule_schema r in
  let s_0 = Option.value_exn (Subst.match_opt (r_0.lhs @ r_0.rhs) (r.lhs @ r.rhs)) in
  let ss = Subst.all_subst_alts s_0 in
  List.fold ss ~init:[] ~f:(fun rs s ->
    let l' = apply r_0.lhs s and r' = apply r_0.rhs s in
    if equiv l' r' then Rewrite_system.insert_max_general {lhs = l'; rhs = r'} rs else rs)

let generate_rules s t =
  let gr = generalize {lhs = s; rhs = t} in
  List.fold (List.concat_map gr ~f:strip) ~init:[]
    ~f:(fun rs r -> if (List.mem rs r ~equal:[%eq: Rule.t]) then rs else r :: rs)
