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
  ]

let () =
  run_test_tt_main suite
