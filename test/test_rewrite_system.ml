open Core
open OUnit2
open Rule
open Rewrite_system

let r_0 = {lhs = [PUSH (Val "0"); PUSH (Val "0"); ADD]; rhs = [PUSH (Val "0")]}
let r_1 = {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]}
let r_2 = {lhs = [PUSH (Const "x"); PUSH (Val "0"); ADD]; rhs = [PUSH (Const "x")]}

let suite = "suite" >::: [

    "Check that order of rules does not matter for equality" >:: (fun _ ->
        let r_1 = {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]}
        and r_2 = {lhs = [PUSH (Const "x"); PUSH (Val "0"); ADD]; rhs = [PUSH (Const "x")]}
        and r_0 = {lhs = [PUSH (Val "0"); PUSH (Val "0"); ADD]; rhs = [PUSH (Val "0")]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r_0; r_1; r_2] [r_1; r_2; r_0]
      );

    "Check that alpha equivalence does not matter for equality" >:: (fun _ ->
        let r_2 = {lhs = [PUSH (Const "x"); PUSH (Val "0"); ADD]; rhs = [PUSH (Const "x")]}
        and r_3 = {lhs = [PUSH (Const "y"); PUSH (Val "0"); ADD]; rhs = [PUSH (Const "y")]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r_2] [r_3]
      );

    "Check that order and alpha do not matter for equality" >:: (fun _ ->
        let r_1 = {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]}
        and r_2 = {lhs = [PUSH (Const "x"); PUSH (Val "0"); ADD]; rhs = [PUSH (Const "x")]}
        and r_0 = {lhs = [PUSH (Val "0"); PUSH (Val "0"); ADD]; rhs = [PUSH (Val "0")]}
        and r_3 = {lhs = [PUSH (Const "y"); PUSH (Val "0"); ADD]; rhs = [PUSH (Const "y")]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r_0; r_3; r_1] [r_1; r_0; r_2]
      );


    "Show system in TPDB format produces expected string" >:: (fun _ ->
        let rs =
          [ {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]}
          ; {lhs = [DUP I; SWAP I]; rhs = []}
          ]
        in
        assert_equal
          ~printer:Fn.id
          "(VAR P x)\n\
           (RULES\n\
           \ \ PUSH(0, PUSH(x, ADD(P))) -> PUSH(x, P)\n\
           \ \ DUP1(SWAP1(P)) -> P\n\
           )"
          (show_tpdb rs)
      );

    (* contains_rule *)

    "Rule is in the rewrite system">:: (fun _ ->
        let r = {lhs = [PUSH (Const "x"); POP]; rhs = []} in
        assert_equal true (contains_rule [r] r)
      );

    "Instance is in the rewrite system">:: (fun _ ->
        let r   = {lhs = [PUSH (Const "x"); POP]; rhs = []} in
        let r_i = {lhs = [PUSH (Const "y"); POP]; rhs = []} in
        assert_equal true (contains_rule [r_i] r)
      );

    "Rule is not in the rewrite system">:: (fun _ ->
        let r = {lhs = [PUSH (Const "x"); POP]; rhs = []} in
        let rs = [{lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]}] in
        assert_equal false (contains_rule rs r)
      );

    "No rule is in the empty rewrite system">:: (fun _ ->
        let r = {lhs = [PUSH (Const "x"); POP]; rhs = []} in
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
        let r_g = {lhs = [PUSH (Const "x"); PUSH (Const "y"); ADD]; rhs = [PUSH (Const "z")]} in
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
