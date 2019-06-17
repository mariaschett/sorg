open Core
open OUnit2
open Rule
open Ebso
open Stackarg
open Instruction

let suite = "suite" >::: [

    (* is_mapped *)

    "Variable is mapped in substitution">::(fun _ ->
        assert_equal true (is_mapped "x" [("x", "y")])
      );

    "Variable is not mapped in empty substitution">::(fun _ ->
        assert_equal false (is_mapped "x" [])
      );

    "Variable is not mapped in substitution">::(fun _ ->
        assert_equal false (is_mapped "x" [("z", "y")])
      );

    (* map_exn *)

    "Map when exists in substitution">::(fun _ ->
        assert_equal
          ~cmp:[%eq: constarg] ~printer:[%show: constarg]
          "y" (map_exn "x" [("x", "y")])
      );

    (* map_extend *)

    "Extend empty substitution">::(fun _ ->
        assert_equal
          ~cmp:[%eq: var_subst] ~printer:[%show: var_subst]
          [("x", "y")] (map_extend "x" "y" [])
      );

    "Extend substitution">::(fun _ ->
        assert_equal
          ~cmp:[%eq: var_subst] ~printer:[%show: var_subst]
          [("x", "y"); ("z", "v")] (map_extend "x" "y" [("z", "v")])
      );

    "Element is mapped in extended substitution">::(fun _ ->
        let s = map_extend "x" "y" [] in
        assert_equal
          true (is_mapped "x" s)
      );

    (* update_var_subst *)

    "Update substitution where same mapping exists">::(fun _ ->
        let s = [("x", "y")] in
        assert_equal
          ~cmp:[%eq: var_subst option] ~printer:[%show: var_subst option]
          (Some s) (update_var_subst "x" "y" s)
      );

    "Update substitution where different mapping exists">::(fun _ ->
        let s = [("x", "y")] in
        let s' = map_extend "z" "v" s in
        assert_equal
          ~cmp:[%eq: var_subst option] ~printer:[%show: var_subst option]
          (Some s') (update_var_subst "z" "v" s)
      );

    "Fail when different mapping is inserted">::(fun _ ->
        let s = [("x", "y")] in
        assert_equal
          ~cmp:[%eq: var_subst option] ~printer:[%show: var_subst option]
          None (update_var_subst "x" "v" s)
      );

    "Fail when two different instructions are at same position">::(fun _ ->
        assert_equal
          ~cmp:[%eq: var_subst option] ~printer:[%show: var_subst option]
          None (compute_var_subst [ADD] [MUL])
      );

    "Succeed on equal programs without PUSH">::(fun _ ->
        assert_equal
          ~cmp:[%eq: var_subst option] ~printer:[%show: var_subst option]
          (Some []) (compute_var_subst [ADD; SUB] [ADD; SUB])
      );

    "Fail on programs with different size">::(fun _ ->
        assert_equal
          ~cmp:[%eq: var_subst option] ~printer:[%show: var_subst option]
          None (compute_var_subst [ADD; SUB] [ADD;])
      );

    "Succeed for PUSH with one argument">::(fun _ ->
        assert_equal
          ~cmp:[%eq: var_subst option] ~printer:[%show: var_subst option]
          (Some [("x", "y")]) (compute_var_subst [PUSH (Const "x")] [PUSH (Const "y");])
      );

    "Succeed for two PUSH with same arguments">::(fun _ ->
        let l1 = [PUSH (Const "x"); PUSH (Const "x")] in
        let l2 = [PUSH (Const "y"); PUSH (Const "y")] in
        assert_equal
          ~cmp:[%eq: var_subst option] ~printer:[%show: var_subst option]
          (Some [("x", "y")]) (compute_var_subst l1 l2)
      );

    "Succeed for two PUSH mapping arguments to same argument">::(fun _ ->
        let l1 = [PUSH (Const "x"); PUSH (Const "y")] in
        let l2 = [PUSH (Const "z"); PUSH (Const "z")] in
        assert_equal
          ~cmp:[%eq: var_subst option] ~printer:[%show: var_subst option]
          (Some [("x", "z"); ("y", "z")]) (compute_var_subst l1 l2)
      );

    "Fail when two argument would need to map to different terms">::(fun _ ->
        let l1 = [PUSH (Const "x"); PUSH (Const "x")] in
        let l2 = [PUSH (Const "y"); PUSH (Const "z")] in
        assert_equal
          ~cmp:[%eq: var_subst option] ~printer:[%show: var_subst option]
          None (compute_var_subst l1 l2)
      );

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
