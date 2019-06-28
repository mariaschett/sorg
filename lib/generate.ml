open Core
open Ebso
open Evmenc
open Z3util
open Instruction
open Rule
open Subst

let is_translation_valid s t =
  let c = enc_trans_val (mk_enc_consts s (`User [])) t in
  match solve_model [c] with
    | None -> true
    | Some _ -> false

let equiv = is_translation_valid

let eq_mod_push_arg i i' = match i, i' with
  | PUSH _, PUSH _ -> true
  | _ -> [%eq: Instruction.t] i i'

let rec strip_prefix r = match r.lhs, r.rhs with
  | i :: s', i' :: t' when eq_mod_push_arg i i' ->
    if equiv s' t'
    then strip_prefix {lhs = s'; rhs = t'}
    else r
  | _ -> r

let rec strip_suffix r = match List.rev (r.lhs), List.rev (r.rhs) with
  | i :: rs', i' :: rt' when eq_mod_push_arg i i' ->
    let s' = List.rev rs' and t' = List.rev rt' in
    if equiv s' t'
    then strip_suffix {lhs = s'; rhs = t'}
    else r
  | _ -> r

let generalize_all r =
  let r_0 = maximal_rule_schema r in
  let s_0 = Option.value_exn (Subst.match_opt (r_0.lhs @ r_0.rhs) (r.lhs @ r.rhs)) in
  let ss = Subst.all_subst_alts s_0 in
  List.fold ss ~init:[] ~f:(fun rs s ->
    let l' = apply r_0.lhs s and r' = apply r_0.rhs s in
    if equiv l' r' then Rewrite_system.insert_max_general {lhs = l'; rhs = r'} rs else rs)

let generalize r =
  let gr = generalize_all r in
  let most_general r = not (List.exists gr ~f:(fun r' ->
      not ([%eq: Rule.t] r r') &&
      is_instance (r.lhs @ r.rhs) (r'.lhs @ r'.rhs))) in
  List.filter gr ~f:most_general

let generate_rules s t =
  let gr = generalize {lhs = s; rhs = t} in
  let pre_suf r = strip_suffix (strip_prefix r) in
  let suf_pre r = strip_prefix (strip_suffix r) in
  List.fold (List.map gr ~f:suf_pre) ~init:(List.map gr ~f:pre_suf) ~f:(fun rs r -> if (List.mem rs r ~equal:[%eq: Rule.t]) then rs else r :: rs)
