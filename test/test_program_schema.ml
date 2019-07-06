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
