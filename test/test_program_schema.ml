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
open Pusharg
open Program_schema

let x = "x" and y = "y" and z = "z"
let x_v = Word (Const x) and y_v = Word (Const y) and z_v = Word (Const z)
let wzero = Word (Val "0")
let wone = Word (Val "1")
let wtwo = Word (Val "2")
let wthree = Word (Val "3")

let suite = "suite" >::: [

    (* alpha_equal *)

    "Fail alpha equvivalence for two PUSH mapping arguments to same argument">::(fun _ ->
        let l1 = [PUSH x_v; PUSH y_v] in
        let l2 = [PUSH z_v; PUSH z_v] in
        assert_equal false (alpha_equal l1 l2)
      );

    "Succeed alpha equvivalence for two PUSH mapping arguments to different arguments">::(fun _ ->
        let l1 = [PUSH x_v; PUSH y_v] in
        let l2 = [PUSH y_v; PUSH x_v] in
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
        let s = [PUSH wtwo; DUP II; SWAP I] and t = [DUP I; PUSH wtwo] in
        assert_bool "" (equiv s t)
      );

    "Remove superflous prefix, abstract PUSH argument" >::(fun _ ->
        let s = [POP; PUSH wthree; SWAP I; POP] in
        let t = [POP; POP; PUSH wthree] in
        assert_bool "" (equiv s t)
      );

    "Generalize PUSH args, two rules" >::(fun _ ->
        let s = [PUSH wzero; PUSH wzero; ADD] in
        let t = [PUSH wzero] in
        assert_bool "" (equiv s t)
      );

    "Advanced constant folding">::(fun _ ->
        let s = [PUSH wone; PUSH wtwo; DUP II; OR] in
        let t = [PUSH wone; PUSH wthree] in
        assert_bool "" (equiv s t)
      );

    "ADD commutative, combines [..]" >::(fun _ ->
        let s = [POP; PUSH wthree; DUP II; ADD; SWAP I; POP; PUSH wtwo] in
        let t = [POP; PUSH wthree; ADD; PUSH wtwo] in
        assert_bool "" (equiv s t)
      );

    "Generalize PUSH args with constants" >::(fun _ ->
        let w = Word (Const "w") in
        let s = [PUSH wzero; PUSH w; ADD] in
        let t = [PUSH w] in
        assert_bool "" (equiv s t)
      );

    "Generalize PUSH args with different constants" >::(fun _ ->
        let s = [PUSH wzero; PUSH (Word (Const "w1")); ADD] in
        let t = [PUSH (Word (Const "w2"))] in
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
        let i = PUSH x_v and x = "x_0" in
        assert_equal
          ~cmp:[%eq: Instruction.t option] ~printer:[%show: Instruction.t option]
          None (instruction_schema x i)
      );

    "PUSH (Val 0) instruction needs to become a schema">::(fun _ ->
        let i = PUSH wzero and x = "x" in
        assert_equal
          ~cmp:[%eq: Instruction.t option] ~printer:[%show: Instruction.t option]
          (Some (PUSH x_v)) (instruction_schema x i)
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
        let c = Word (Const "c") in
        let p = [PUSH wone; PUSH wthree; PUSH c] in
        let p' = [PUSH (Word (Const "x_1")); PUSH (Word (Const "x_2")); PUSH c] in
        assert_equal
        ~cmp:(fun (i, p) (i', p') -> i = i' && alpha_equal p p')
        ~printer:[%show: int * Program_schema.t]
        (2, p') (maximal_schema 0 p)
      );
  ]

let () =
  run_test_tt_main suite
