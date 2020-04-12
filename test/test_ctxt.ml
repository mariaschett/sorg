(*   Copyright 2019 Maria A Schett and Julian Nagele

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
open OUnit2
open Ebso
open Ctxt
open Instruction.T
open Pusharg

let comp_ctxts cs cs' =
  let sort = List.sort Ctxt.compare in
  [%eq: Ctxt.t list] (sort cs) (sort cs')

let show_ctxts cs =
  let sort = List.sort Ctxt.compare in
  [%show: Ctxt.t list] (sort cs)

let x = "x" and y = "y" and z = "z"
let x_v = Word (Const x) and y_v = Word (Const y) and z_v = Word (Const z)

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
        let s = [PUSH x_v] in
        let t = [PUSH y_v] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [] (all_ctxts s t)
      );

    "Programs with same immediate arguments" >:: (fun _ ->
        let s = [PUSH x_v] in
        let t = [PUSH x_v] in
        assert_equal
          ~cmp:comp_ctxts
          ~printer:show_ctxts
          [([], [])] (all_ctxts s t)
      );

    "A different program has no context" >:: (fun _ ->
        let s = [PUSH x_v] in
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
        let s = [PUSH x_v] and t = [PUSH y_v] in
        assert_equal ~cmp:[%eq: Program_schema.t] ~printer:[%show: Program_schema.t]
          [] (common_prefix s t)
      );

    (* common_postfix *)

    "No common postfix for PUSHs">::(fun _ ->
        let s = [PUSH x_v] and t = [PUSH y_v] in
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
