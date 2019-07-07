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
open Rule
open Generate
open Ebso
open Instruction
open OUnit2

let suite = "suite" >::: [

    (* strip *)

    "Remove superflous prefix" >::(fun _ ->
        let r = {lhs = [POP; PUSH (Val "0"); ADD]; rhs = [POP]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [{lhs = [PUSH (Val "0"); ADD]; rhs = []}] (strip r)
      );

    "Removing prefix is not correct" >::(fun _ ->
        let r = {lhs = [CALLVALUE; DUP I]; rhs = [CALLVALUE; CALLVALUE]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r] (strip r)
      );

    "Remove superflous suffix" >::(fun _ ->
        let r = {lhs = [PUSH (Val "0"); ADD; POP]; rhs = [POP]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [{lhs = [PUSH (Val "0"); ADD]; rhs = []}] (strip r)
      );

    "Removing suffix is not correct" >::(fun _ ->
        let r = {lhs = [PUSH (Val "2"); POP]; rhs = [ADDRESS; POP]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r] (strip r)
      );

    (* generate_rules *)

    "Remove superflous suffix" >::(fun _ ->
        let s = [CALLVALUE; DUP I; ISZERO] in
        let t = [CALLVALUE; CALLVALUE; ISZERO] in
        let r = {lhs = [CALLVALUE; DUP I];
                 rhs = [CALLVALUE; CALLVALUE]}
        in
        assert_equal ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r] (generate_rules s t)
      );

    "Generalize PUSH argument" >::(fun _ ->
        let s = [PUSH (Val "2"); DUP II; SWAP I] and t = [DUP I; PUSH (Val "2")] in
        let r = { lhs = [PUSH (Const "c"); DUP II; SWAP I];
                  rhs = [DUP I; PUSH (Const "c")]}
        in
        assert_equal
          ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r] (generate_rules s t)
      );

    "Remove superflous prefix, abstract PUSH argument" >::(fun _ ->
        let s = [POP; PUSH (Val "3"); SWAP I; POP] in
        let t = [POP; POP; PUSH (Val "3")] in
        let r = { lhs = [PUSH (Const "c"); SWAP I; POP];
                  rhs = [POP; PUSH (Const "c")]}
        in
        assert_equal ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r] (generate_rules s t)
      );

    "Generalize PUSH args, two rules" >::(fun _ ->
        let s = [PUSH (Val "0"); PUSH (Val "0"); ADD] in
        let t = [PUSH (Val "0")] in
        let r1 = { lhs = [PUSH (Val "0"); PUSH (Const "c"); ADD];
                   rhs = [PUSH (Const "c")]} in
        let r2 = { lhs = [PUSH (Val "0"); ADD];
                   rhs = []}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t]
          ~printer:[%show: Rewrite_system.t]
          [r1; r2] (generate_rules s t)
      );

    "Advanced constant folding">::(fun _ ->
        let s = [PUSH (Val "1"); PUSH (Val "2"); DUP II; OR] in
        let t = [PUSH (Val "1"); PUSH (Val "3")]
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t]
          ~printer:[%show: Rewrite_system.t]
          [{lhs = s; rhs = t}] (generate_rules s t)
      );

    "ADD commutative, combines remove pre-/suffix and generate rules argument" >::(fun _ ->
        let s = [POP; PUSH (Val "3"); SWAP I; ADD; PUSH (Val "2")] in
        let t = [POP; PUSH (Val "3"); ADD; PUSH (Val "2")] in
        let r = { lhs = [SWAP I; ADD];
                  rhs = [ADD] }
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r] (generate_rules s t)
      );

    "Mix ADD, DUP, and SWAP" >::(fun _ ->
        let s = [POP; PUSH (Val "3"); DUP II; ADD; SWAP I; POP; PUSH (Val "2")] in
        let t = [POP; PUSH (Val "3"); ADD; PUSH (Val "2")] in
        let r = { lhs = [DUP II; ADD; SWAP I; POP];
                  rhs = [ADD] }
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r] (generate_rules s t)
      );

    "Mix ADDRESS, DUP and POP" >:: (fun _ ->
        let s = [ADDRESS; DUP I; POP] in
        let t = [ADDRESS; ADDRESS; POP] in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [{lhs = [ADDRESS; DUP I]; rhs = [ADDRESS; ADDRESS]};
           {lhs = [DUP I; POP]; rhs = [ADDRESS; POP]}]
          (generate_rules s t)
      );

    (* generalize *)

    "Find the two generalizations from PUSH 0 PUSH 0 ADD to PUSH 0">:: (fun _ ->
        let r = {lhs = [PUSH (Val "0"); PUSH (Val "0"); ADD]; rhs = [PUSH (Val "0")]} in
        assert_equal
          ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [ {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]}
          ; {lhs = [PUSH (Const "x"); PUSH (Val "0"); ADD]; rhs = [PUSH (Const "x")]}
          ]
          (generalize r)
      );

    "No generalization possible">::(fun _ ->
        let s = [PUSH (Val "0"); ADD] and t = [] in
        let r = {lhs = s; rhs = t}
        in
        assert_equal
           ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r] (generalize r)
      );

    "Find generalization for one variable" >:: (fun _ ->
        let r = {lhs = [PUSH (Val "0")]; rhs = [PUSH (Val "0")]} in
        let rs = generalize r in
        assert_equal
           ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [{lhs = [PUSH (Const "x")]; rhs = [PUSH (Const "x")]}]
          rs
      );

    "Generalize program with stack-depth > 0" >:: (fun _ ->
        let r = {lhs = [POP; PUSH (Val "3"); PUSH (Val "0"); ADD];
                 rhs = [POP; PUSH (Val "3")]} in
        assert_equal
          ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [ {lhs = [POP; PUSH (Const "x"); PUSH (Val "0"); ADD] ;
             rhs = [POP; PUSH (Const "x")]};]
          (generalize r)
      );

    "Generalize incorrect optimization" >:: (fun _ ->
        let r = {lhs = [DUP I; PUSH (Val "3"); EQ];
                 rhs = [PUSH (Val "1")]} in
        assert_equal
          ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          []
          (generalize r)
      );

  ]

let () =
  run_test_tt_main suite
