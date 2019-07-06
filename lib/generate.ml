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

let rec strip' rs r = function
  | [] -> rs
  | (i,j) :: idx ->
    let l' = Ctxt.strip_ctxt i j r.lhs and r' = Ctxt.strip_ctxt i j r.rhs in
    if equiv l' r'
    then
      let rs' = {lhs = l'; rhs = r'} :: rs in
      let idx' = List.filter idx ~f:(fun (i',j') -> not (i' < i && j' < j)) in
      strip' rs' r idx'
    else
      let idx' = List.filter idx ~f:(fun (i',j') -> not (i' > i && j' > j) ) in
      strip' rs r idx'

let strip r =
  let k = List.length (Ctxt.common_prefix r.lhs r.rhs) in
  let m = List.length (Ctxt.common_postfix r.lhs r.rhs) in
  let idxs = Subst.n_cartesian_product [(List.init (k+1) ~f:Fn.id);(List.init (m+1) ~f:Fn.id)] in
  let idxs_pairs = List.map idxs ~f:(fun idx -> match idx with [i; j] -> (i,j) | _ -> failwith "strip_all" ) in
  let sr = strip' [] r idxs_pairs in
  let most_context r = not (List.exists sr ~f:(fun r' ->
      not ([%eq: Rule.t] r r') &&
      is_subrule r' r))
  in
  List.filter sr ~f:most_context

let rec generalize' rs r_0 t = function
  | [] -> rs
  | s :: ss ->
    let l' = apply r_0.lhs s and r' = apply r_0.rhs s in
    if equiv l' r'
    then
      let rs' = Rewrite_system.insert_max_general {lhs = l'; rhs = r'} rs in
      let ss' = rm_less_general t s ss in
      generalize' rs' r_0 t ss'
    else
      let ss' = rm_more_general t s ss in
      generalize' rs r_0 t ss'

let generalize r =
  let r_0 = maximal_rule_schema r in
  let s_0 = Option.value_exn (Subst.match_opt (r_0.lhs @ r_0.rhs) (r.lhs @ r.rhs)) in
  let ss = List.sort (Subst.all_subst_alts s_0) ~compare:(fun s s' -> Subst.compare s' s) in
  generalize' [] r_0 (r_0.lhs @ r_0.rhs) ss

let generate_rules s t =
  let gr = generalize {lhs = s; rhs = t} in
  List.fold (List.concat_map gr ~f:strip) ~init:[]
    ~f:(fun rs r -> if (List.mem rs r ~equal:[%eq: Rule.t]) then rs else r :: rs)
