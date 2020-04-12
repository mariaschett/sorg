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
open OUnit2
open Sorg
open Rule
open Rewrite_system
open Ebso
open Pusharg

let x = "x" and y = "y" and z = "z"
let x_v = Word (Const x) and y_v = Word (Const y) and z_v = Word (Const z)
let wzero = Word (Val "0")


let r_0 = {lhs = [PUSH wzero; PUSH wzero; ADD]; rhs = [PUSH wzero]}
let r_1 = {lhs = [PUSH wzero; PUSH x_v; ADD]; rhs = [PUSH x_v]}
let r_2 = {lhs = [PUSH x_v; PUSH wzero; ADD]; rhs = [PUSH x_v]}

let suite = "suite" >::: [

    "Check that order of rules does not matter for equality" >:: (fun _ ->
        let r_1 = {lhs = [PUSH wzero; PUSH x_v; ADD]; rhs = [PUSH x_v]}
        and r_2 = {lhs = [PUSH x_v; PUSH wzero; ADD]; rhs = [PUSH x_v]}
        and r_0 = {lhs = [PUSH wzero; PUSH wzero; ADD]; rhs = [PUSH wzero]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r_0; r_1; r_2] [r_1; r_2; r_0]
      );

    "Check that alpha equivalence does not matter for equality" >:: (fun _ ->
        let r_2 = {lhs = [PUSH x_v; PUSH wzero; ADD]; rhs = [PUSH x_v]}
        and r_3 = {lhs = [PUSH y_v; PUSH wzero; ADD]; rhs = [PUSH y_v]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r_2] [r_3]
      );

    "Check that order and alpha do not matter for equality" >:: (fun _ ->
        let r_1 = {lhs = [PUSH wzero; PUSH x_v; ADD]; rhs = [PUSH x_v]}
        and r_2 = {lhs = [PUSH x_v; PUSH wzero; ADD]; rhs = [PUSH x_v]}
        and r_0 = {lhs = [PUSH wzero; PUSH wzero; ADD]; rhs = [PUSH wzero]}
        and r_3 = {lhs = [PUSH y_v; PUSH wzero; ADD]; rhs = [PUSH y_v]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r_0; r_3; r_1] [r_1; r_0; r_2]
      );


    "Show system in TPDB format produces expected string" >:: (fun _ ->
        let rs =
          [ {lhs = [PUSH wzero; PUSH x_v; ADD]; rhs = [PUSH x_v]}
          ; {lhs = [DUP I; SWAP I]; rhs = []}
          ]
        in
        assert_equal
          ~printer:Fn.id
          "(VAR P cx)\n\
           (RULES\n\
           \ \ PUSH(0, PUSH(cx, ADD(P))) -> PUSH(cx, P)\n\
           \ \ DUP1(SWAP1(P)) -> P\n\
           )"
          (show_tpdb rs)
      );

    (* contains_rule *)

    "Rule is in the rewrite system">:: (fun _ ->
        let r = {lhs = [PUSH x_v; POP]; rhs = []} in
        assert_equal true (contains_rule [r] r)
      );

    "Instance is in the rewrite system">:: (fun _ ->
        let r   = {lhs = [PUSH x_v; POP]; rhs = []} in
        let r_i = {lhs = [PUSH y_v; POP]; rhs = []} in
        assert_equal true (contains_rule [r_i] r)
      );

    "Rule is not in the rewrite system">:: (fun _ ->
        let r = {lhs = [PUSH x_v; POP]; rhs = []} in
        let rs = [{lhs = [PUSH wzero; PUSH x_v; ADD]; rhs = [PUSH x_v]}] in
        assert_equal false (contains_rule rs r)
      );

    "No rule is in the empty rewrite system">:: (fun _ ->
        let r = {lhs = [PUSH x_v; POP]; rhs = []} in
        assert_equal false (contains_rule [] r)
      );

    (* size *)

    "Empty rewrite system has size 0">:: (fun _ ->
        assert_equal 0 (size [])
      );

    "Rewrite system of size 3">:: (fun _ ->
        assert_equal 3 (size [r_1; r_2; r_0])
      );

    (* insert_max_general *)

    "Insert rule in empty">:: (fun _ ->
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
        [r_1] (insert_max_general r_1 [])
      );

    "Insert more general rule">:: (fun _ ->
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
        [r_1] (insert_max_general r_1 [r_0])
      );

    "Insert less general rule">:: (fun _ ->
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
        [r_1] (insert_max_general r_0 [r_1])
      );

    "Insert incompatible rule">:: (fun _ ->
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
        [r_1; r_2] (insert_max_general r_2 [r_1])
      );

    "Insert rule more general than both">:: (fun _ ->
        let r_g = {lhs = [PUSH x_v; PUSH y_v; ADD]; rhs = [PUSH z_v]} in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
        [r_g] (insert_max_general r_g [r_1; r_2])
      );

    (* insert_non_dup_rules *)

    "Check that a fresh rule is inserted" >:: (fun _ ->
        assert_equal ~cmp:[%eq: Rewrite_system.t * Rewrite_system.t]
          ~printer:[%show: Rewrite_system.t * Rewrite_system.t]
          ([r_0; r_1], []) (insert_non_dup_rules [r_0] [r_1])
      );

    "Check that a duplicate rule is not inserted" >:: (fun _ ->
        assert_equal ~cmp:[%eq: Rewrite_system.t * Rewrite_system.t]
          ~printer:[%show: Rewrite_system.t * Rewrite_system.t]
          ([r_1], [r_1]) (insert_non_dup_rules [r_1] [r_1])
      );

    "Check that multiple rules are inserted correctly" >:: (fun _ ->
        assert_equal ~cmp:[%eq: Rewrite_system.t * Rewrite_system.t]
          ~printer:[%show: Rewrite_system.t * Rewrite_system.t]
          ([r_0; r_1; r_2], [r_1]) (insert_non_dup_rules [r_1; r_0; r_2] [r_1])
      );

    "Check that multiple duplicates are kept correctly" >:: (fun _ ->
        assert_equal ~cmp:[%eq: Rewrite_system.t * Rewrite_system.t]
          ~printer:[%show: Rewrite_system.t * Rewrite_system.t]
          ([r_0; r_1], [r_1; r_1; r_0]) (insert_non_dup_rules [r_1; r_0; r_1; r_0] [r_1])
      );

  ]

let () =
  run_test_tt_main suite
