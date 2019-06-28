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
          "(VAR x)\n\
           (RULES\n\
           \ \ PUSH(0, PUSH(x, ADD(P))) -> PUSH(x, P)\n\
           \ \ DUP1(SWAP1(P)) -> P\n\
           )"
          (show_tpdb rs)
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
  ]

let () =
  run_test_tt_main suite
