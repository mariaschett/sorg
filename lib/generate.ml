open Core
open Ebso
open Evmenc
open Z3util
open Rule
open Generalize

let is_translation_valid s t =
  let c = enc_trans_val (mk_enc_consts s (`User [])) t in
  match solve_model [c] with
    | None -> true
    | Some _ -> false

let equiv = is_translation_valid

let rec strip_prefix r = match r.lhs, r.rhs with
  | _ :: s', _ :: t' ->
    if equiv s' t'
    then strip_prefix {lhs = s'; rhs = t'}
    else r
  | _ -> r

let rec strip_suffix r = match List.rev (r.lhs), List.rev (r.rhs) with
  | _ :: rs', _ :: rt' ->
    let s' = List.rev rs' and t' = List.rev rt' in
    if equiv s' t'
    then strip_suffix {lhs = s'; rhs = t'}
    else r
  | _ -> r

let generate_rules s t =
  let gr = generalize {lhs = s; rhs = t} in
  let pre_suf r = strip_suffix (strip_prefix r) in
  let suf_pre r = strip_prefix (strip_suffix r) in
  List.fold (List.map gr ~f:suf_pre) ~init:(List.map gr ~f:pre_suf) ~f:(fun rs r -> if (List.mem rs r ~equal:[%eq: Rule.t]) then rs else r :: rs)
