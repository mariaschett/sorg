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
open Ebso
open Instruction
open Program_schema

let suite = "suite" >::: [

    (* alpha_equal *)

    "Fail alpha equvivalence for two PUSH mapping arguments to same argument">::(fun _ ->
        let l1 = [PUSH (Const "x"); PUSH (Const "y")] in
        let l2 = [PUSH (Const "z"); PUSH (Const "z")] in
        assert_equal false (alpha_equal l1 l2)
      );

    "Succeed alpha equvivalence for two PUSH mapping arguments to different arguments">::(fun _ ->
        let l1 = [PUSH (Const "x"); PUSH (Const "y")] in
        let l2 = [PUSH (Const "y"); PUSH (Const "x")] in
        assert_equal true (alpha_equal l1 l2)
      );

    (* equiv *)

    "Two equal constant terms are equvivalent">::(fun _ ->
        let s = [DUP I] and t = [DUP I]
        in
        assert_bool "" (equiv s t)
      );

    "Remove superflous suffix" >::(fun _ ->
        let s = [CALLVALUE; DUP I; ISZERO] in
        let t = [CALLVALUE; CALLVALUE; ISZERO]
        in
        assert_bool "" (equiv s t)
      );

    "Generalize PUSH argument" >::(fun _ ->
        let s = [PUSH (Val "2"); DUP II; SWAP I] and t = [DUP I; PUSH (Val "2")] in
        assert_bool "" (equiv s t)
      );

    "Remove superflous prefix, abstract PUSH argument" >::(fun _ ->
        let s = [POP; PUSH (Val "3"); SWAP I; POP] in
        let t = [POP; POP; PUSH (Val "3")] in
        assert_bool "" (equiv s t)
      );

    "Generalize PUSH args, two rules" >::(fun _ ->
        let s = [PUSH (Val "0"); PUSH (Val "0"); ADD] in
        let t = [PUSH (Val "0")] in
        assert_bool "" (equiv s t)
      );

    "Advanced constant folding">::(fun _ ->
        let s = [PUSH (Val "1"); PUSH (Val "2"); DUP II; OR] in
        let t = [PUSH (Val "1"); PUSH (Val "3")] in
        assert_bool "" (equiv s t)
      );

    "ADD commutative, combines [..]" >::(fun _ ->
        let s = [POP; PUSH (Val "3"); DUP II; ADD; SWAP I; POP; PUSH (Val "2")] in
        let t = [POP; PUSH (Val "3"); ADD; PUSH (Val "2")] in
        assert_bool "" (equiv s t)
      );

    "Generalize PUSH args with constants" >::(fun _ ->
        let s = [PUSH (Val "0"); PUSH (Const "w"); ADD] in
        let t = [PUSH (Const "w")] in
        assert_bool "" (equiv s t)
      );

    "Generalize PUSH args with different constants" >::(fun _ ->
        let s = [PUSH (Val "0"); PUSH (Const "w1"); ADD] in
        let t = [PUSH (Const "w2")] in
        assert_bool "" (not (equiv s t))
      );

    (* instruction_schema *)

    "Non-PUSH is a schema">::(fun _ ->
        let i = ADD and x = "x_0" in
        assert_equal
          ~cmp:[%eq: Instruction.t option] ~printer:[%show: Instruction.t option]
          None (instruction_schema x i)
      );

    "PUSH (Const x) instruction is already a schema">::(fun _ ->
        let i = PUSH (Const "x") and x = "x_0" in
        assert_equal
          ~cmp:[%eq: Instruction.t option] ~printer:[%show: Instruction.t option]
          None (instruction_schema x i)
      );

    "PUSH (Val 0) instruction needs to become a schema">::(fun _ ->
        let i = PUSH (Val "0") and x = "x_0" in
        assert_equal
          ~cmp:[%eq: Instruction.t option] ~printer:[%show: Instruction.t option]
          (Some (PUSH (Const x))) (instruction_schema x i)
      );

    (* maximal_schema *)

    "Empty program is a maximal program schema">::(fun _ ->
        let p = [] in
        assert_equal
          ~cmp:[%eq: int * Program_schema.t] ~printer:[%show: int * Program_schema.t]
          (0, p) (maximal_schema 0 p)
      );

    "A program without PUSH is a maximal program schema">::(fun _ ->
        let p = [DUP I; SWAP I] in
        assert_equal
          ~cmp:[%eq: int * Program_schema.t] ~printer:[%show: int * Program_schema.t]
          (0, p) (maximal_schema 0 p)
      );

    "Compute a program schema with PUSH (Val n) and PUSH (Const c)">::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "3"); PUSH (Const "c")] in
        let p' = [PUSH (Const "x_1"); PUSH (Const "x_2"); PUSH (Const "c")] in
        assert_equal
        ~cmp:(fun (i, p) (i', p') -> i = i' && alpha_equal p p')
        ~printer:[%show: int * Program_schema.t]
        (2, p') (maximal_schema 0 p)
      );
  ]

let () =
  run_test_tt_main suite
