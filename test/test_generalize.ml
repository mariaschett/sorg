open Generalize
open Ebso
open Instruction
open OUnit2

let suite = "suite" >::: [

    "Generalize equal constant term" >::(fun _ ->
        let s = [DUP I] and t = [DUP I]
        in
        assert_equal
          ~cmp:[%eq: (Program.t * Program.t) list]
          ~printer:[%show: (Program.t * Program.t) list]
          [(s, t)] (generalize s t)
      );

    "Remove superflous suffix" >::(fun _ ->
        let s = [CALLVALUE; DUP I; ISZERO] in
        let t = [CALLVALUE; CALLVALUE; ISZERO] in
        let l = [CALLVALUE; DUP I] and r = [CALLVALUE; CALLVALUE]
        in
        assert_equal ~cmp:[%eq: (Program.t * Program.t) list]
          ~printer:[%show: (Program.t * Program.t) list]
          [(l, r)] (generalize s t)
      );

    "Abstract PUSH argument" >::(fun _ ->
        let s = [PUSH (Val "2"); DUP II; SWAP I] and t = [DUP I; PUSH (Val "2")] in
        let l = [PUSH (Const "c"); DUP II; SWAP I] and r = [DUP I; PUSH (Const "c")]
        in
        assert_equal
          ~cmp:[%eq: (Program.t * Program.t) list]
          ~printer:[%show: (Program.t * Program.t) list]
          [(l, r)] (generalize s t)
      );

    "Remove superflous prefix, abstract PUSH argument" >::(fun _ ->
        let s = [POP; PUSH (Val "3"); SWAP I; POP] in
        let t = [POP; POP; PUSH (Val "3")] in
        let l = [PUSH (Const "c"); SWAP I; POP] and r = [POP; PUSH (Const "c")]
        in
        assert_equal ~cmp:[%eq: (Program.t * Program.t) list]
          ~printer:[%show: (Program.t * Program.t) list]
          [(l, r)] (generalize s t)
      );

    "Abstract PUSH args, two rules" >::(fun _ ->
        let s = [PUSH (Val "0"); PUSH (Val "0"); ADD] in
        let t = [PUSH (Val "0")] in
        let l1 = [PUSH (Val "0"); PUSH (Const "c"); ADD] in
        let l2 = [PUSH (Const "c"); PUSH (Val "0"); ADD] in
        let r = [PUSH (Const "c")]
        in
        assert_equal ~cmp:[%eq: (Program.t * Program.t) list]
          ~printer:[%show: (Program.t * Program.t) list]
          [(l1, r); (l2, r)] (generalize s t)
      );

    "Advanced constant folding">::(fun _ ->
        let s = [PUSH (Val "1"); PUSH (Val "2"); DUP II; OR] in
        let t = [PUSH (Val "1"); PUSH (Val "3")]
        in
        assert_equal ~cmp:[%eq: (Program.t * Program.t) list]
          ~printer:[%show: (Program.t * Program.t) list]
          [(s, t)] (generalize s t)
      );

    "ADD commutative, combines remove pre-/suffix and generalize argument" >::(fun _ ->
        let s = [POP; PUSH (Val "3"); DUP II; ADD; SWAP I; POP; PUSH (Val "2")] in
        let t = [POP; PUSH (Val "3"); ADD; PUSH (Val "2")] in
        let l = [PUSH (Const "c"); DUP II; ADD] in
        let r = [PUSH (Const "c")]
        in
        assert_equal ~cmp:[%eq: (Program.t * Program.t) list]
          ~printer:[%show: (Program.t * Program.t) list]
          [(l, r)] (generalize s t)
      );
  ]

let () =
  run_test_tt_main suite
