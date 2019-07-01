open OUnit2
open Ebso
open Ctxt
open Instruction

let suite = "suite" >::: [

    (* apply *)

    "Apply empty context">::(fun _ ->
        let s = [POP] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          s (apply ([], []) s)
      );

    "Apply context with prefix">::(fun _ ->
        let s = [POP] in
        let pre = [ADD] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          (pre @ s) (apply (pre, []) s)
      );

    "Apply context with postfix">::(fun _ ->
        let s = [POP] in
        let post = [ADD] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          (s @ post) (apply ([], post) s)
      );

    "Apply context">::(fun _ ->
        let s = [POP] in
        let pre = [SUB] in
        let post = [ADD] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          (pre @ s @ post) (apply (pre, post) s)
      );
  ]

let () =
  run_test_tt_main suite
