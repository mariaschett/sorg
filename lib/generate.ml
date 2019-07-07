(*   Copyright 2019 Maria A Schett and Julian Nagele

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
open Core
open Rule

let rec generalize' rs r_0 t = function
  | [] -> rs
  | s :: ss ->
    let l' = Subst.apply r_0.lhs s and r' = Subst.apply r_0.rhs s in
    if Program_schema.equiv l' r'
    then
      let rs' = Rewrite_system.insert_max_general {lhs = l'; rhs = r'} rs in
      let ss' = Subst.rm_less_general t s ss in
      generalize' rs' r_0 t ss'
    else
      let ss' = Subst.rm_more_general t s ss in
      generalize' rs r_0 t ss'

let generalize r =
  let r_0 = maximal_rule_schema r in
  let s_0 = Option.value_exn (Subst.match_opt (r_0.lhs @ r_0.rhs) (r.lhs @ r.rhs)) in
  let ss = List.sort (Subst.all_subst_alts s_0) ~compare:(fun s s' -> Subst.compare s' s) in
  generalize' [] r_0 (r_0.lhs @ r_0.rhs) ss

let rec strip' rs r = function
  | [] -> rs
  | (i, j) :: idx ->
    if i + j > List.length r.lhs || i + j > List.length r.rhs then
      strip' rs r idx
    else
      let l' = Ctxt.strip_ctxt i j r.lhs and r' = Ctxt.strip_ctxt i j r.rhs in
      if Program_schema.equiv l' r'
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
  let idxs = Util.cartesian_product_up_to k m in
  let sr = strip' [] r idxs in
  let most_context r = not (List.exists sr ~f:(fun r' ->
      not ([%eq: Rule.t] r r') &&
      is_subrule r' r))
  in
  List.filter sr ~f:most_context

let generate_rules s t =
  let gr = generalize {lhs = s; rhs = t} in
  List.fold (List.concat_map gr ~f:strip) ~init:[]
    ~f:(fun rs r -> if (List.mem rs r ~equal:[%eq: Rule.t]) then rs else r :: rs)
