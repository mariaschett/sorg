open OUnit2
open Ebso
open Ctxt
open Instruction

let comp_ctxts cs cs' =
  let sort = List.sort Ctxt.compare in
  [%eq: Ctxt.t list] (sort cs) (sort cs')

let show_ctxts cs =
  let sort = List.sort Ctxt.compare in
  [%show: Ctxt.t list] (sort cs)

let suite = "suite" >::: [

    (* apply *)

    "Apply empty context">::(fun _ ->
        let s = [POP] in
        assert_equal
          ~cmp:[%eq: Program_schema.t]
          ~printer:[%show: Program_schema.t]
          s (apply ([], []) s)
      );

    "Apply context with prefix">::(fun _ ->
        let s = [POP] in
        let pre = [ADD] in
        assert_equal
          ~cmp:[%eq: Program_schema.t]
          ~printer:[%show: Program_schema.t]
          (pre @ s) (apply (pre, []) s)
      );

    "Apply context with postfix">::(fun _ ->
        let s = [POP] in
        let post = [ADD] in
        assert_equal
          ~cmp:[%eq: Program_schema.t]
          ~printer:[%show: Program_schema.t]
          (s @ post) (apply ([], post) s)
      );

    "Apply context">::(fun _ ->
        let s = [POP] in
        let pre = [SUB] in
        let post = [ADD] in
        assert_equal
          ~cmp:[%eq: Program_schema.t]
          ~printer:[%show: Program_schema.t]
          (pre @ s @ post) (apply (pre, post) s)
      );

    (* all_ctxts *)

    "Context of program itself is empty" >:: (fun _ ->
        let s = [POP] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [([],[])] (all_ctxts s s)
      );

    "The empty program contains no non-empty program" >:: (fun _ ->
        let s = [POP] in
        let t = [] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [] (all_ctxts s t)
      );

    "Every program contains the empty program" >:: (fun _ ->
        let s = [] in
        let t = [POP] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [([], t); (t, [])] (all_ctxts s t)
      );

    "Context is only prefix" >:: (fun _ ->
        let s = [POP] in
        let t = [ADD; POP] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [([ADD], []);] (all_ctxts s t)
      );

    "Context is only postfix" >:: (fun _ ->
        let s = [POP] in
        let t = [POP; ADD] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [([], [ADD]);] (all_ctxts s t)
      );

    "Context is pre- and postfix" >:: (fun _ ->
        let s = [POP] in
        let t = [ADD; POP; ADD] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [([ADD], [ADD]);] (all_ctxts s t)
      );

    "Program is contained via two different contexts" >:: (fun _ ->
        let s = [POP] in
        let t = [POP; POP] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [([], [POP]); ([POP], [])] (all_ctxts s t)
      );

    "Program is contained via three different contexts" >:: (fun _ ->
        let s = [POP] in
        let t = [POP; POP; POP] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [([], [POP;POP]); ([POP; POP], []); ([POP], [POP])] (all_ctxts s t)
      );

    "Programs with different immediate arguments (although instances)" >:: (fun _ ->
        let s = [PUSH (Const "x")] in
        let t = [PUSH (Const "y")] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [] (all_ctxts s t)
      );

    "Programs with same immediate arguments" >:: (fun _ ->
        let s = [PUSH (Const "x")] in
        let t = [PUSH (Const "x")] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [([], [])] (all_ctxts s t)
      );

    "A different program has no context" >:: (fun _ ->
        let s = [PUSH (Const "x")] in
        let t = [POP] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [] (all_ctxts s t)
      );

    (* strip_ctxt *)

    "Do not strip anything">::(fun _ ->
        let t = [POP] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          t (strip_ctxt 0 0 t)
      );

    "Remove prefix">::(fun _ ->
        let t = [POP] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          [] (strip_ctxt 1 0 t)
      );

    "Remove postfix">::(fun _ ->
        let t = [POP] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          [] (strip_ctxt 0 1 t)
      );

    "Remove pre- and postfix">::( fun _ ->
        let t = [POP; POP; POP] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          [POP] (strip_ctxt 1 1 t)
      );

    "Remove too much of pre- and postfix">::(fun _ ->
        let t = [POP; POP; POP] in
        assert_raises Not_enough_context (fun () -> strip_ctxt 2 2 t)
      );

    (* common_prefix *)

    "No common prefix">::(fun _ ->
        let s = [POP] and t = [ADD] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          [] (common_prefix s t)
      );

    "Common prefix of length 1">::(fun _ ->
        let s = [POP] and t = [POP; ADD] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          [POP] (common_prefix s t)
      );

    "Common prefix of empty programs">::(fun _ ->
        let s = [] and t = [] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          [] (common_prefix s t)
      );

    "Common prefix of length n">::(fun _ ->
        let s = [POP; POP] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          s (common_prefix s s)
      );

    "Common prefix, but different programs">::(fun _ ->
        let s = [POP; ADD] and t = [POP; SUB] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          [POP] (common_prefix s t)
      );

    "No common prefix for PUSHs">::(fun _ ->
        let s = [PUSH (Const "x")] and t = [PUSH (Const "y")] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          [] (common_prefix s t)
      );

    (* common_postfix *)

    "No common postfix for PUSHs">::(fun _ ->
        let s = [PUSH (Const "x")] and t = [PUSH (Const "y")] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          [] (common_postfix s t)
      );

    "Common postfixs with remainder">::(fun _ ->
        let s = [ADD; ADD; POP] and t = [SUB; ADD; POP] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          [ADD; POP] (common_postfix s t)
      );
  ]

let () =
  run_test_tt_main suite
