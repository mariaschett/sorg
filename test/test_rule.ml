open Core
open OUnit2
open Rule
open Ebso
open Instruction

let suite = "suite" >::: [

    (* alpha equvivalence *)

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
        let r1 = {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]}
        in
        assert_equal true ([%eq: Rule.t] r1 r1)
      );

    "PUSH 0 PUSH x ADD to PUSH x is equal to PUSH 0 PUSH y ADD to PUSH y" >::(fun _ ->
        let r1 = {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]} in
        let r2 = {lhs = [PUSH (Val "0"); PUSH (Const "y"); ADD]; rhs = [PUSH (Const "y")]}
        in
        assert_equal true ([%eq: Rule.t] r1 r2)
      );

    "Show produces expected rule" >::(fun _ ->
        let r = {lhs = [DUP I; SWAP I]; rhs = []}
        in
        assert_equal
          ~printer:Fn.id
          "DUP1 SWAP1 -> " ([%show: Rule.t] r)
      );

    (* abstract instruction *)

    "Non-PUSH is not abstracted">::(fun _ ->
        let i = ADD and w = "w_0" in
        assert_equal
          ~cmp:[%eq: Instruction.t option] ~printer:[%show: Instruction.t option]
          None (abstract_instruction w i)
      );

    "PUSH (Const x) instruction is already abstract and not abstracted">::(fun _ ->
        let i = PUSH (Const "x") and w = "w_0" in
        assert_equal
          ~cmp:[%eq: Instruction.t option] ~printer:[%show: Instruction.t option]
          None (abstract_instruction w i)
      );

    "PUSH (Val 0) instruction is abstracted">::(fun _ ->
        let i = PUSH (Val "0") and w = "w_0" in
        assert_equal
          ~cmp:[%eq: Instruction.t option] ~printer:[%show: Instruction.t option]
          (Some (PUSH (Const w))) (abstract_instruction w i)
      );

    (* abstract program *)

    "Abstract empty program">::(fun _ ->
        let p = [] in
        assert_equal
          ~cmp:[%eq: int * Program.t] ~printer:[%show: int * Program.t]
          (0, p) (abstract_program 0 p)
      );

    "Abstract program without PUSH">::(fun _ ->
        let p = [DUP I; SWAP I] in
        assert_equal
          ~cmp:[%eq: int * Program.t] ~printer:[%show: int * Program.t]
          (0, p) (abstract_program 0 p)
      );

    "Abstract program with PUSH (Val n) and PUSH (Const c) instructions">::(fun _ ->
        let p = [PUSH (Val "1"); PUSH (Val "3"); PUSH (Const "c")] in
        let p' = [PUSH (Const "w_1"); PUSH (Const "w_2"); PUSH (Const "c")] in
        assert_equal
        ~cmp:(fun (i, p) (i', p') -> i = i' && alpha_equal p p')
        ~printer:[%show: int * Program.t]
        (2, p') (abstract_program 0 p)
      );

    (* abstract rule *)

    "Abstract rule with only PUSH (Val n)">::(fun _ ->
        let r = {lhs = [PUSH (Val "0"); PUSH (Val "0"); ADD]; rhs = [PUSH (Val "0")]} in
        let r' = {lhs = [PUSH (Const "w_1"); PUSH (Const "w_2"); ADD]; rhs = [PUSH (Const "w_3")]} in
        assert_equal
          ~cmp:[%eq: Rule.t] ~printer:[%show: Rule.t]
          r' (abstract_rule r)
      );

    "Abstract rule with PUSH (Val n) and PUSH (Const x)">::(fun _ ->
        let r = {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]} in
        let r' = {lhs = [PUSH (Const "w_1"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]} in
        assert_equal
          ~cmp:[%eq: Rule.t] ~printer:[%show: Rule.t]
          r' (abstract_rule r)
      );

    "Show system in TPDB format produces expected string" >:: (fun _ ->
        let rs =
          [ {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]}
          ; {lhs = [DUP I; SWAP I]; rhs = []}
          ]
        in
        assert_equal
          ~printer:Fn.id
          "(VAR x)\n\
           (RULES\n\
           \ \ PUSH(0, PUSH(x, ADD(P))) -> PUSH(x, P)\n\
           \ \ DUP1(SWAP1(P)) -> P\n\
           )"
          (Rule.show_tpdb_system rs)
      );
  ]

let () =
  run_test_tt_main suite
