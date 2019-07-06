open Core
open OUnit2
open Rule
open Ebso
open Instruction

let suite = "suite" >::: [

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
          "DUP1 SWAP1 => " ([%show: Rule.t] r)
      );

    (* maximal_rule_schema *)

    "Compute a rule schema with only PUSH (Val n)">::(fun _ ->
        let r = {lhs = [PUSH (Val "0"); PUSH (Val "0"); ADD];
                 rhs = [PUSH (Val "0")]} in
        let r' = {lhs = [PUSH (Const "x_1"); PUSH (Const "x_2"); ADD];
                  rhs = [PUSH (Const "x_3")]} in
        assert_equal
          ~cmp:[%eq: Rule.t] ~printer:[%show: Rule.t]
          r' (maximal_rule_schema r)
      );

    "Compute a rule with PUSH (Val n) and PUSH (Const x)">::(fun _ ->
        let r = {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD];
                 rhs = [PUSH (Const "x")]} in
        let r' = {lhs = [PUSH (Const "x_1"); PUSH (Const "x"); ADD];
                  rhs = [PUSH (Const "x")]} in
        assert_equal
          ~cmp:[%eq: Rule.t] ~printer:[%show: Rule.t]
          r' (maximal_rule_schema r)
      );

    (* match_opt *)

    "Find substitituion between general program and instantiated program">::(fun _ ->
        let gr = {lhs = [PUSH (Const "x"); PUSH (Const "y"); ADD];
                  rhs = [PUSH (Const "z")]} in
        let sr = {lhs = [PUSH (Val "0"); PUSH (Val "0"); ADD];
                  rhs = [PUSH (Val "0")]} in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
        (Some [("x", Val "0"); ("y", Val "0"); ("z", Val "0")]) (match_opt gr sr)
      );

    (* is_subrule *)

    "A rule is a subrule of itself" >:: (fun _ ->
        let r = {lhs = [PUSH (Val "0"); ADD]; rhs = []} in
        assert_bool "should be a subrule" (is_subrule r r )
      );

    "Adding a prefix results in a subrule" >:: (fun _ ->
        let r = {lhs = [PUSH (Val "0"); ADD]; rhs = []} in
        let c = ([POP], []) in
        let r' = {lhs = Ctxt.apply c r.lhs; rhs = Ctxt.apply c r.rhs} in
        assert_bool "should be a subrule" (is_subrule r r')
      );

    "Adding a postfix results in a subrule" >:: (fun _ ->
        let r = {lhs = [PUSH (Val "0"); ADD]; rhs = []} in
        let c = ([], [SUB]) in
        let r' = {lhs = Ctxt.apply c r.lhs; rhs = Ctxt.apply c r.rhs} in
        assert_bool "should be a subrule" (is_subrule r r')
      );

    "Adding a context results in a subrule" >:: (fun _ ->
        let r = {lhs = [PUSH (Val "0"); ADD]; rhs = []} in
        let c = ([POP], [SUB]) in
        let r' = {lhs = Ctxt.apply c r.lhs; rhs = Ctxt.apply c r.rhs} in
        assert_bool "should be a subrule" (is_subrule r r')
      );

    "Different ways of being a subrule" >:: (fun _ ->
        let r = {lhs = [PUSH (Val "0"); ADD]; rhs = []} in
        let r' = {lhs = [PUSH (Val "0"); ADD; PUSH (Val "0"); ADD];
                  rhs = [PUSH (Val "0"); ADD]} in
        assert_bool "should be a subrule" (is_subrule r r')
      );

    "Having different contexts on lhs and rhs is not a subrule" >:: (fun _ ->
        let r = {lhs = [PUSH (Val "0"); ADD]; rhs = []} in
        let r' = {lhs = [PUSH (Val "0"); ADD; PUSH (Val "0"); ADD]; rhs = []} in
        assert_bool "should not be a subrule" (not @@ is_subrule r r')
      );

    "Subrule with PUSH" >:: (fun _ ->
        let r = {lhs = [PUSH (Const "w_1"); SWAP I; POP];
                 rhs = [POP; PUSH (Const "w_1")]} in
        let r' = {lhs = [POP; PUSH (Const "w_1"); SWAP I; POP];
                  rhs = [POP; POP; PUSH (Const "w_1")]} in
        assert_bool "should be a subrule" (is_subrule r r')
      );

  ]

let () =
  run_test_tt_main suite
