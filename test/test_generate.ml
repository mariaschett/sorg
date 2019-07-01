open Rule
open Generate
open Ebso
open Instruction
open OUnit2
open Core

let suite = "suite" >::: [

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

    (* strip_all *)

    "Remove superflous prefix" >::(fun _ ->
        let r = {lhs = [POP; PUSH (Val "0"); ADD]; rhs = [POP]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r; {lhs = [PUSH (Val "0"); ADD]; rhs = []}] (strip_all r)
      );

    "Removing prefix is not correct" >::(fun _ ->
        let r = {lhs = [CALLVALUE; DUP I]; rhs = [CALLVALUE; CALLVALUE]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r] (strip_all r)
      );

    "Remove superflous suffix" >::(fun _ ->
        let r = {lhs = [PUSH (Val "0"); ADD; POP]; rhs = [POP]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r; {lhs = [PUSH (Val "0"); ADD]; rhs = []}] (strip_all r)
      );

    "Removing suffix is not correct" >::(fun _ ->
        let r = {lhs = [PUSH (Val "2"); POP]; rhs = [ADDRESS; POP]}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r] (strip_all r)
      );

    "Three rules from same context">::(fun _ ->
        let r = {lhs = [PUSH (Val "0"); ADD]; rhs = []}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [ {lhs = [POP] @ r.lhs @ [POP]; rhs = [POP] @ r.rhs @ [POP]};
            {lhs = r.lhs @ [POP]; rhs = r.rhs @ [POP]};
            {lhs = [POP] @ r.lhs; rhs = [POP] @ r.rhs};
            r;
          ]
          (strip_all {lhs = [POP] @ r.lhs @ [POP]; rhs = [POP] @ r.rhs @ [POP]})
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
        let s = [PUSH (Val "2"); DUP II; SWAP I] and t = [DUP I; PUSH (Val "2")] in
        let r = { lhs = [PUSH (Const "c"); DUP II; SWAP I];
                  rhs = [DUP I; PUSH (Const "c")]}
        in
        assert_equal
          ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r] (generate_rules s t)
      );

    "Remove superflous prefix, abstract PUSH argument" >::(fun _ ->
        let s = [POP; PUSH (Val "3"); SWAP I; POP] in
        let t = [POP; POP; PUSH (Val "3")] in
        let r = { lhs = [PUSH (Const "c"); SWAP I; POP];
                  rhs = [POP; PUSH (Const "c")]}
        in
        assert_equal ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r] (generate_rules s t)
      );

    "Generalize PUSH args, two rules" >::(fun _ ->
        let s = [PUSH (Val "0"); PUSH (Val "0"); ADD] in
        let t = [PUSH (Val "0")] in
        let r1 = { lhs = [PUSH (Val "0"); PUSH (Const "c"); ADD];
                   rhs = [PUSH (Const "c")]} in
        let r2 = { lhs = [PUSH (Val "0"); ADD];
                   rhs = []}
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t]
          ~printer:[%show: Rewrite_system.t]
          [r1; r2] (generate_rules s t)
      );

    "Advanced constant folding">::(fun _ ->
        let s = [PUSH (Val "1"); PUSH (Val "2"); DUP II; OR] in
        let t = [PUSH (Val "1"); PUSH (Val "3")]
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t]
          ~printer:[%show: Rewrite_system.t]
          [{lhs = s; rhs = t}] (generate_rules s t)
      );

    "ADD commutative, combines remove pre-/suffix and generate rules argument" >::(fun _ ->
        let s = [POP; PUSH (Val "3"); SWAP I; ADD; PUSH (Val "2")] in
        let t = [POP; PUSH (Val "3"); ADD; PUSH (Val "2")] in
        let r = { lhs = [SWAP I; ADD];
                  rhs = [ADD] }
        in
        assert_equal ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [r] (generate_rules s t)
      );

    "Mix ADD, DUP, and SWAP" >::(fun _ ->
        let s = [POP; PUSH (Val "3"); DUP II; ADD; SWAP I; POP; PUSH (Val "2")] in
        let t = [POP; PUSH (Val "3"); ADD; PUSH (Val "2")] in
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
        let r = {lhs = [PUSH (Val "0"); PUSH (Val "0"); ADD]; rhs = [PUSH (Val "0")]} in
        assert_equal
          ~cmp:[%eq: Rewrite_system.t] ~printer:[%show: Rewrite_system.t]
          [ {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]}
          ; {lhs = [PUSH (Const "x"); PUSH (Val "0"); ADD]; rhs = [PUSH (Const "x")]}
          ]
          (generalize r)
      );
  ]

let () =
  run_test_tt_main suite
