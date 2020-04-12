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
open Sorg
open Rule
open Generate
open Ebso
open Instruction.T
open Pusharg
open OUnit2

let wzero = Word (Val "0")
let wone = Word (Val "1")
let wtwo = Word (Val "2")
let wthree = Word (Val "3")
let wconstx = Word (Const "x")
let wconstc = Word (Const "c")

let suite = "suite" >::: [

    (* strip *)

    "Remove superflous prefix" >::(fun _ ->
        let r = {lhs = [POP; PUSH wzero; ADD]; rhs = [POP]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [{lhs = [PUSH wzero; ADD]; rhs = []}] (strip r)
      );

    "Removing prefix is not correct" >::(fun _ ->
        let r = {lhs = [CALLVALUE; DUP I]; rhs = [CALLVALUE; CALLVALUE]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r] (strip r)
      );

    "Remove superflous suffix" >::(fun _ ->
        let r = {lhs = [PUSH wzero; ADD; POP]; rhs = [POP]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [{lhs = [PUSH wzero; ADD]; rhs = []}] (strip r)
      );

    "Removing suffix is not correct" >::(fun _ ->
        let r = {lhs = [PUSH wtwo; POP]; rhs = [ADDRESS; POP]}
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
        let s = [PUSH wtwo; DUP II; SWAP I] and t = [DUP I; PUSH wtwo] in
        let r = { lhs = [PUSH wconstc; DUP II; SWAP I];
                  rhs = [DUP I; PUSH wconstc]}
        in
        assert_equal
          ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r] (generate_rules s t)
      );

    "Remove superflous prefix, abstract PUSH argument" >::(fun _ ->
        let s = [POP; PUSH wthree; SWAP I; POP] in
        let t = [POP; POP; PUSH wthree] in
        let r = { lhs = [PUSH wconstc; SWAP I; POP];
                  rhs = [POP; PUSH wconstc]}
        in
        assert_equal ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r] (generate_rules s t)
      );

    "Generalize PUSH args, two rules" >::(fun _ ->
        let s = [PUSH wzero; PUSH wzero; ADD] in
        let t = [PUSH wzero] in
        let r1 = { lhs = [PUSH wzero; PUSH wconstc; ADD];
                   rhs = [PUSH wconstc]} in
        let r2 = { lhs = [PUSH wzero; ADD];
                   rhs = []}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t]
          ~printer:[%show: Rewrite_system.t]
          [r1; r2] (generate_rules s t)
      );

    "Advanced constant folding">::(fun _ ->
        let s = [PUSH wone; PUSH wtwo; DUP II; OR] in
        let t = [PUSH wone; PUSH wthree]
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t]
          ~printer:[%show: Rewrite_system.t]
          [{lhs = s; rhs = t}] (generate_rules s t)
      );

    "ADD commutative, combines remove pre-/suffix and generate rules argument" >::(fun _ ->
        let s = [POP; PUSH wthree; SWAP I; ADD; PUSH wtwo] in
        let t = [POP; PUSH wthree; ADD; PUSH wtwo] in
        let r = { lhs = [SWAP I; ADD];
                  rhs = [ADD] }
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r] (generate_rules s t)
      );

    "Mix ADD, DUP, and SWAP" >::(fun _ ->
        let s = [POP; PUSH wthree; DUP II; ADD; SWAP I; POP; PUSH wtwo] in
        let t = [POP; PUSH wthree; ADD; PUSH wtwo] in
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
        let r = {lhs = [PUSH wzero; PUSH wzero; ADD]; rhs = [PUSH wzero]} in
        assert_equal
          ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [ {lhs = [PUSH wzero; PUSH wconstx; ADD]; rhs = [PUSH wconstx]}
          ; {lhs = [PUSH wconstx; PUSH wzero; ADD]; rhs = [PUSH wconstx]}
          ]
          (generalize r)
      );

    "No generalization possible">::(fun _ ->
        let s = [PUSH wzero; ADD] and t = [] in
        let r = {lhs = s; rhs = t}
        in
        assert_equal
           ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r] (generalize r)
      );

    "Find generalization for one variable" >:: (fun _ ->
        let r = {lhs = [PUSH wzero]; rhs = [PUSH wzero]} in
        let rs = generalize r in
        assert_equal
           ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [{lhs = [PUSH wconstx]; rhs = [PUSH wconstx]}]
          rs
      );

    "Generalize program with stack-depth > 0" >:: (fun _ ->
        let r = {lhs = [POP; PUSH wthree; PUSH wzero; ADD];
                 rhs = [POP; PUSH wthree]} in
        assert_equal
          ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [ {lhs = [POP; PUSH wconstx; PUSH wzero; ADD] ;
             rhs = [POP; PUSH wconstx]};]
          (generalize r)
      );

    "Generalize incorrect optimization" >:: (fun _ ->
        let r = {lhs = [DUP I; PUSH wthree; EQ];
                 rhs = [PUSH wone]} in
        assert_equal
          ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          []
          (generalize r)
      );

  ]

let () =
  run_test_tt_main suite
