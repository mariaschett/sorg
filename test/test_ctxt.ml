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
  ]

let () =
  run_test_tt_main suite
