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
open Rule
open Ebso
open Instruction
open Pusharg

let x = "x" and y = "y" and z = "z"
let x_v = Word (Const x) and y_v = Word (Const y) and z_v = Word (Const z)
let wzero = Word (Val "0")


let suite = "suite" >::: [

    "Rule is equal to itself" >::(fun _ ->
        let r = {lhs = [DUP I; SWAP I]; rhs = []}
        in
        assert_equal true ([%eq: Rule.t] r r)
      );

    "Two different rules are not equal" >::(fun _ ->
        let r1 = {lhs = [DUP I; SWAP I]; rhs = []} in
        let r2 = {lhs = [DUP I; POP]; rhs = []}
        in
        assert_equal false ([%eq: Rule.t] r1 r2)
      );

    "PUSH 0 PUSH x ADD to PUSH x is equal to itself" >::(fun _ ->
        let r1 = {lhs = [PUSH wzero; PUSH x_v; ADD]; rhs = [PUSH x_v]}
        in
        assert_equal true ([%eq: Rule.t] r1 r1)
      );

    "PUSH 0 PUSH x ADD to PUSH x is equal to PUSH 0 PUSH y ADD to PUSH y" >::(fun _ ->
        let r1 = {lhs = [PUSH wzero; PUSH x_v; ADD]; rhs = [PUSH x_v]} in
        let r2 = {lhs = [PUSH wzero; PUSH y_v; ADD]; rhs = [PUSH y_v]}
        in
        assert_equal true ([%eq: Rule.t] r1 r2)
      );

    "Show produces expected rule" >::(fun _ ->
        let r = {lhs = [DUP I; SWAP I]; rhs = []}
        in
        assert_equal
          ~printer:Fn.id
          "DUP1 SWAP1 => " ([%show: Rule.t] r)
      );

    (* maximal_rule_schema *)

    "Compute a rule schema with only PUSH (Val n)">::(fun _ ->
        let r = {lhs = [PUSH wzero; PUSH wzero; ADD];
                 rhs = [PUSH wzero]} in
        let r' = {lhs = [PUSH (Word (Const "x_1")); PUSH (Word (Const "x_2")); ADD];
                  rhs = [PUSH (Word (Const "x_3"))]} in
        assert_equal
          ~cmp:[%eq: Rule.t] ~printer:[%show: Rule.t]
          r' (maximal_rule_schema r)
      );

    "Compute a rule with PUSH (Val n) and PUSH (Const x)">::(fun _ ->
        let r = {lhs = [PUSH wzero; PUSH x_v; ADD];
                 rhs = [PUSH x_v]} in
        let r' = {lhs = [PUSH (Word (Const "x_1")); PUSH x_v; ADD];
                  rhs = [PUSH x_v]} in
        assert_equal
          ~cmp:[%eq: Rule.t] ~printer:[%show: Rule.t]
          r' (maximal_rule_schema r)
      );

    (* is_subrule *)

    "A rule is a subrule of itself" >:: (fun _ ->
        let r = {lhs = [PUSH wzero; ADD]; rhs = []} in
        assert_bool "should be a subrule" (is_subrule r r )
      );

    "Adding a prefix results in a subrule" >:: (fun _ ->
        let r = {lhs = [PUSH wzero; ADD]; rhs = []} in
        let c = ([POP], []) in
        let r' = {lhs = Ctxt.apply c r.lhs; rhs = Ctxt.apply c r.rhs} in
        assert_bool "should be a subrule" (is_subrule r r')
      );

    "Adding a postfix results in a subrule" >:: (fun _ ->
        let r = {lhs = [PUSH wzero; ADD]; rhs = []} in
        let c = ([], [SUB]) in
        let r' = {lhs = Ctxt.apply c r.lhs; rhs = Ctxt.apply c r.rhs} in
        assert_bool "should be a subrule" (is_subrule r r')
      );

    "Adding a context results in a subrule" >:: (fun _ ->
        let r = {lhs = [PUSH wzero; ADD]; rhs = []} in
        let c = ([POP], [SUB]) in
        let r' = {lhs = Ctxt.apply c r.lhs; rhs = Ctxt.apply c r.rhs} in
        assert_bool "should be a subrule" (is_subrule r r')
      );

    "Different ways of being a subrule" >:: (fun _ ->
        let r = {lhs = [PUSH wzero; ADD]; rhs = []} in
        let r' = {lhs = [PUSH wzero; ADD; PUSH wzero; ADD];
                  rhs = [PUSH wzero; ADD]} in
        assert_bool "should be a subrule" (is_subrule r r')
      );

    "Having different contexts on lhs and rhs is not a subrule" >:: (fun _ ->
        let r = {lhs = [PUSH wzero; ADD]; rhs = []} in
        let r' = {lhs = [PUSH wzero; ADD; PUSH wzero; ADD]; rhs = []} in
        assert_bool "should not be a subrule" (not @@ is_subrule r r')
      );

    "Subrule with PUSH" >:: (fun _ ->
        let r = {lhs = [PUSH x_v; SWAP I; POP];
                 rhs = [POP; PUSH x_v]} in
        let r' = {lhs = [POP; PUSH x_v; SWAP I; POP];
                  rhs = [POP; POP; PUSH x_v]} in
        assert_bool "should be a subrule" (is_subrule r r')
      );

  ]

let () =
  run_test_tt_main suite
