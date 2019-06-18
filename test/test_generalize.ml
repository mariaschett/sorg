open Rule
open Generalize
open Ebso
open Instruction
open OUnit2

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

    "Abstract PUSH argument" >::(fun _ ->
        let s = [PUSH (Val "2"); DUP II; SWAP I] and t = [DUP I; PUSH (Val "2")] in
        assert_bool "" (equiv s t)
      );

    "Remove superflous prefix, abstract PUSH argument" >::(fun _ ->
        let s = [POP; PUSH (Val "3"); SWAP I; POP] in
        let t = [POP; POP; PUSH (Val "3")] in
        assert_bool "" (equiv s t)
      );

    "Abstract PUSH args, two rules" >::(fun _ ->
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

    "Abstract PUSH args with constants" >::(fun _ ->
        let s = [PUSH (Val "0"); PUSH (Const "w"); ADD] in
        let t = [PUSH (Const "w")] in
        assert_bool "" (equiv s t)
      );

    "Abstract PUSH args with different constants" >::(fun _ ->
        let s = [PUSH (Val "0"); PUSH (Const "w1"); ADD] in
        let t = [PUSH (Const "w2")] in
        assert_bool "" (not (equiv s t))
      );

    (* drop prefix *)

    "Remove superflous prefix" >::(fun _ ->
        let s = [POP; PUSH (Val "0"); ADD] in
        let t = [POP]
        in
        assert_equal ~cmp:[%eq: Program.t * Program.t]
          ~printer:[%show: Program.t * Program.t]
          ([PUSH (Val "0"); ADD], []) (drop_prefix s t)
      );

    "Removing prefix is not correct" >::(fun _ ->
        let s = [CALLVALUE; DUP I] in
        let t = [CALLVALUE; CALLVALUE]
        in
        assert_equal ~cmp:[%eq: Program.t * Program.t]
          ~printer:[%show: Program.t * Program.t]
          (s, t) (drop_prefix s t)
      );

    (* remove suffix *)

    "Remove superflous suffix" >::(fun _ ->
        let s = [PUSH (Val "0"); ADD; POP] in
        let t = [POP]
        in
        assert_equal ~cmp:[%eq: Program.t * Program.t]
          ~printer:[%show: Program.t * Program.t]
          ([PUSH (Val "0"); ADD], []) (drop_suffix s t)
      );

    "Removing suffix is not correct" >::(fun _ ->
        let s = [PUSH (Val "2"); POP] in
        let t = [ADDRESS; POP]
        in
        assert_equal ~cmp:[%eq: Program.t * Program.t]
          ~printer:[%show: Program.t * Program.t]
          (s, t) (drop_suffix s t)
      );

    (* generalize *)

    "Remove superflous suffix" >::(fun _ ->
        todo "generalize not implemented";
        let s = [CALLVALUE; DUP I; ISZERO] in
        let t = [CALLVALUE; CALLVALUE; ISZERO] in
        let r = {lhs = [CALLVALUE; DUP I];
                 rhs = [CALLVALUE; CALLVALUE]}
        in
        assert_equal ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r] (generalize s t)
      );

    "Abstract PUSH argument" >::(fun _ ->
        todo "generalize not implemented";
        let s = [PUSH (Val "2"); DUP II; SWAP I] and t = [DUP I; PUSH (Val "2")] in
        let r = { lhs = [PUSH (Const "c"); DUP II; SWAP I];
                  rhs = [DUP I; PUSH (Const "c")]}
        in
        assert_equal
          ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r] (generalize s t)
      );

    "Remove superflous prefix, abstract PUSH argument" >::(fun _ ->
        todo "generalize not implemented";
        let s = [POP; PUSH (Val "3"); SWAP I; POP] in
        let t = [POP; POP; PUSH (Val "3")] in
        let r = { lhs = [PUSH (Const "c"); SWAP I; POP];
                  rhs = [POP; PUSH (Const "c")]}
        in
        assert_equal ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r] (generalize s t)
      );

    "Abstract PUSH args, two rules" >::(fun _ ->
        todo "generalize not implemented";
        let s = [PUSH (Val "0"); PUSH (Val "0"); ADD] in
        let t = [PUSH (Val "0")] in
        let r1 = { lhs = [PUSH (Val "0"); PUSH (Const "c"); ADD];
                   rhs = [PUSH (Const "c")]} in
        let r2 = { lhs = [PUSH (Const "c"); PUSH (Val "0"); ADD];
                   rhs = [PUSH (Const "c")]}
        in
        assert_equal ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r1; r2] (generalize s t)
      );

    "Advanced constant folding">::(fun _ ->
        todo "generalize not implemented";
        let s = [PUSH (Val "1"); PUSH (Val "2"); DUP II; OR] in
        let t = [PUSH (Val "1"); PUSH (Val "3")]
        in
        assert_equal ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [{lhs = s; rhs = t}] (generalize s t)
      );

    "ADD commutative, combines remove pre-/suffix and generalize argument" >::(fun _ ->
        todo "generalize not implemented";
        let s = [POP; PUSH (Val "3"); DUP II; ADD; SWAP I; POP; PUSH (Val "2")] in
        let t = [POP; PUSH (Val "3"); ADD; PUSH (Val "2")] in
        let r = { lhs = [PUSH (Const "c"); DUP II; ADD];
                  rhs = [PUSH (Const "c")] }
        in
        assert_equal ~cmp:[%eq: Rule.t list]
          ~printer:[%show: Rule.t list]
          [r] (generalize s t)
      );
  ]

let () =
  run_test_tt_main suite
