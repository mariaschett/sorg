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
open Core
open OUnit2
open Ebso
open Stackarg
open Instruction
open Subst

let x = "x" and y = "y" and z = "z"
let x_v = Const x and y_v = Const y and z_v = Const z

let comp_vvars vs vs' =
  let sort = List.sort ~compare:compare_vvar in
  [%eq: vvar list] (sort vs) (sort vs')

let show_vvars vs =
  let sort = List.sort ~compare:compare_vvar in
  [%show: vvar list] (sort vs)

let suite = "suite" >::: [

    (* dom *)

    "Domain of empty substitution is empyty">::(fun _ ->
        assert_equal [] (dom [])
      );

    "Domain of substitution">::(fun _ ->
        assert_equal
          ~cmp:comp_vvars ~printer:show_vvars
          [x; y] (dom [(x, Val "0"); (y, Val "0")])
      );

    (* in_dom *)

    "Variable is mapped in substitution">::(fun _ ->
        assert_equal true (in_dom x [(x, y)])
      );

    "Variable is not mapped in empty substitution">::(fun _ ->
        assert_equal false (in_dom x [])
      );

    "Variable is not mapped in substitution">::(fun _ ->
        assert_equal false (in_dom x [(z, y)])
      );

    (* maps_to_exn *)

    "Map when exists in substitution">::(fun _ ->
        assert_equal
          ~cmp:[%eq: vval] ~printer:[%show: vval]
          y_v (maps_to_exn x [(x, y_v)])
      );

    (* extend_maps_to *)

    "Extend empty substitution">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t] ~printer:[%show: Subst.t]
          [(x, y_v)] (extend_maps_to x y_v [])
      );

    "Extend substitution">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t] ~printer:[%show: Subst.t]
          [(x, y_v); (z, Const "v")] (extend_maps_to x y_v [(z, Const "v")])
      );

    "Element is mapped in extended substitution">::(fun _ ->
        let s = extend_maps_to x "y" [] in
        assert_equal
          true (in_dom x s)
      );

    (* match_instruction *)

    "Match instruction where same mapping exists">::(fun _ ->
        let s = [(x, y_v)] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some s) (match_instruction (Some s) (PUSH (Const x)) (PUSH y_v))
      );

    "Match instruction where unrelated mapping exists">::(fun _ ->
        let s = [(x, y_v)] in
        let s' = extend_maps_to z (Const "v") s in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some s') (match_instruction (Some s) (PUSH (Const z)) (PUSH (Const "v")))
      );

    "Fail when different mapping is inserted">::(fun _ ->
        let s = [(x, y_v)] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (match_instruction (Some s) (PUSH (Const x)) (PUSH (Const "v")))
      );

    "Fail when two different instructions are at same position">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (match_opt [ADD] [MUL])
      );

    "Succeed on equal programs without PUSH">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some []) (match_opt [ADD; SUB] [ADD; SUB])
      );

    "Fail on programs with different size">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (match_opt [ADD; SUB] [ADD;])
      );

    "Succeed for PUSH with one argument">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some [(x, y_v)]) (match_opt [PUSH x_v] [PUSH y_v])
      );

    "Succeed for two PUSH with same arguments">::(fun _ ->
        let l1 = [PUSH x_v; PUSH x_v] in
        let l2 = [PUSH y_v; PUSH y_v] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some [(x, y_v)]) (match_opt l1 l2)
      );

    "Succeed for two PUSH mapping arguments to same argument">::(fun _ ->
        let l1 = [PUSH x_v; PUSH y_v] in
        let l2 = [PUSH z_v; PUSH z_v] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some [(x, z_v); (y, z_v)]) (match_opt l1 l2)
      );

    "Fail when two argument would need to map to different terms">::(fun _ ->
        let l1 = [PUSH x_v; PUSH x_v] in
        let l2 = [PUSH y_v; PUSH z_v] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (match_opt l1 l2)
      );

    "Map PUSH argument to value">::(fun _ ->
        let l1 = [PUSH x_v] in
        let l2 = [PUSH (Val "0")] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some [(x, Val "0")]) (match_opt l1 l2)
      );

    (* maps_to_val *)

    "Variable maps to value">::(fun _ ->
        let s = [("x", Val "0")] in
        assert_equal true (maps_to_val "x" (Val "0") s)
      );

    "Variable does not map to value">::(fun _ ->
        let s = [("x", Val "0")] in
        assert_equal false (maps_to_val "x" (Val "1") s)
      );

    "Variable is not in domain of substitution">::(fun _ ->
        let s = [("x", Val "0")] in
        assert_equal false (maps_to_val "y" (Val "0") s)
      );

    (* preimages_of_val *)

    "No variable maps to value">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "1")] in
        assert_equal
          ~cmp:[%eq: vvar list] ~printer:[%show: vvar list]
          [] (preimages_of_val (Val "2") s)
      );

    "Only one variable maps to value">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "1")] in
        assert_equal
          ~cmp:[%eq: vvar list] ~printer:[%show: vvar list]
          ["y"] (preimages_of_val (Val "1") s)
      );

    "Two variables map to same">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "0")] in
        assert_equal
          ~cmp:(fun xs ys -> [%eq: vvar list]
                   (List.sort ~compare:compare_vvar xs)
                   (List.sort ~compare:compare_vvar ys))
          ~printer:[%show: vvar list]
          ["x"; "y"] (preimages_of_val (Val "0") s)
      );

    "Two variables map to same, one different">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "0"); ("z", Val "1");] in
        assert_equal
          ~cmp:(fun xs ys -> [%eq: vvar list]
                   (List.sort ~compare:compare_vvar xs)
                   (List.sort ~compare:compare_vvar ys))
          ~printer:[%show: vvar list]
          ["x"; "y"] (preimages_of_val (Val "0") s)
      );

    (* apply *)

    "Apply empty substitiution">::(fun _ ->
        let s = [] in
        let p = [PUSH (Const "x")] in
        assert_equal
          ~cmp:[%eq: Program_schema.t]
          ~printer:[%show: Program_schema.t]
          p (apply p s)
      );

    "Apply substitiution on variable in program">::(fun _ ->
        let s = [("x", Val "0")] in
        let p = [PUSH (Const "x")] in
        assert_equal
          ~cmp:[%eq: Program_schema.t]
          ~printer:[%show: Program_schema.t]
          [PUSH (Val "0")] (apply p s)
      );

    "Apply substitiution where variable is not in program">::(fun _ ->
        let s = [("y", Val "0")] in
        let p = [PUSH (Const "x")] in
        assert_equal
          ~cmp:[%eq: Program_schema.t]
          ~printer:[%show: Program_schema.t]
          p (apply p s)
      );

    "Apply substitiution on program without PUSH">::(fun _ ->
        let s = [("x", Val "0")] in
        let p = [ADD] in
        assert_equal
          ~cmp:[%eq: Program_schema.t]
          ~printer:[%show: Program_schema.t]
          p (apply p s)
      );

    "Apply substitiution twice">::(fun _ ->
        let s = [("x", Val "0")] in
        let p = [PUSH (Const "x"); PUSH (Const "x")] in
        assert_equal
          ~cmp:[%eq: Program_schema.t]
          ~printer:[%show: Program_schema.t]
          [PUSH (Val "0"); PUSH (Val "0")] (apply p s)
      );

    (* is_instance *)

    "ADD is not an instance of PUSH x">::(fun _ ->
        assert_equal false (is_instance [ADD] [PUSH (Const "x")])
      );

    "PUSH 0 is an instance of PUSH x">::(fun _ ->
        assert_equal true (is_instance [PUSH (Val "0")] [PUSH (Const "x")])
      );

    "PUSH x is not an instance of PUSH 0">::(fun _ ->
        assert_equal false (is_instance [PUSH (Const "x")] [PUSH (Val "0")])
      );

    "[PUSH 0; PUSH 0] is an instance of [PUSH x; PUSH y]">::(fun _ ->
        assert_equal true (is_instance
                             [PUSH (Val "0"); PUSH (Val "0")]
                             [PUSH (Const "x"); PUSH (Const "y")]
                          )
      );

    "[PUSH 1; PUSH 0] is an not instance of [PUSH x; PUSH x]">::(fun _ ->
        assert_equal false (is_instance
                              [PUSH (Val "1"); PUSH (Val "0")]
                              [PUSH (Const "x"); PUSH (Const "x")]
                           )
      );

    "[PUSH x; PUSH y] is an not instance of [PUSH x; PUSH x]">::(fun _ ->
        assert_equal false (is_instance
                              [PUSH (Const "x"); PUSH (Const "y")]
                              [PUSH (Const "x"); PUSH (Const "x")]
                           )
      );

    "[PUSH y; PUSH x] is an not instance of [PUSH x; PUSH x]">::(fun _ ->
        assert_equal false (is_instance
                              [PUSH (Const "y"); PUSH (Const "x")]
                              [PUSH (Const "x"); PUSH (Const "x")]
                           )
      );

    (* same_image_larger *)

    "Make same_image_larger for x" >::(fun _ ->
        let s = [("x",Val "0"); ("y",Val "0"); ("z",Val "0")] in
        assert_equal
          ~cmp:[%eq: vvar list]
          ~printer:[%show: vvar list]
          ["y"; "z"] (same_image_larger "x" s)
      );

    "Make same_image_larger for y" >::(fun _ ->
        let s = [("x",Val "0"); ("y",Val "0"); ("z",Val "0")] in
        assert_equal
          ~cmp:[%eq: vvar list]
          ~printer:[%show: vvar list]
          ["z"] (same_image_larger "y" s)
      );

    "Make same_image_larger for z" >::(fun _ ->
        let s = [("x",Val "0"); ("y",Val "0"); ("z",Val "0")] in
        assert_equal
          ~cmp:[%eq: vvar list]
          ~printer:[%show: vvar list]
          [] (same_image_larger "z" s)
      );

    (* binding_alts *)

    "Binding alternatives for single binding">::(fun _ ->
        let s = [("x", Val "0")] in
        assert_equal
          ~cmp:[%eq: Subst.t]
          ~printer:[%show: Subst.t]
          [("x", Val "0"); ("x", Const "x")] (binding_alts "x" s)
      );

    "Binding alternatives for two variables mapping to different">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "1")] in
        assert_equal
          ~cmp:[%eq: Subst.t]
          ~printer:[%show: Subst.t]
          [("x", Val "0"); ("x", Const "x")] (binding_alts "x" s)
      );

    "Binding alternatives for two variables mapping to same for larger variable">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "0")] in
        assert_equal
          ~cmp:[%eq: Subst.t]
          ~printer:[%show: Subst.t]
          [("x", Val "0"); ("x", Const "x"); ("x", Const "y")] (binding_alts "x" s)
      );

    "Binding alternatives for two variables mapping to same for smaller variable">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "0")] in
        assert_equal
          ~cmp:[%eq: Subst.t]
          ~printer:[%show: Subst.t]
          [("y", Val "0"); ("y", Const "y")] (binding_alts "y" s)
      );

    (* all_binding_alts *)

    "All binding alternatives contain subst for largest x">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "0"); ("z", Val "1");] in
        let x_alt = [("x", Val "0"); ("x", Const "x"); ("x", Const "y")] in
        assert_equal
          true
          (List.mem (all_binding_alts s) x_alt ~equal:[%eq: Subst.t])
      );

    "All binding alternatives contain subst for smaller y">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "0"); ("z", Val "1");] in
        let y_alt = [("y", Val "0"); ("y", Const "y")] in
        assert_equal
          true
          (List.mem (all_binding_alts s) y_alt ~equal:[%eq: Subst.t])
      );

    "All binding alternatives contain subst for different z">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "0"); ("z", Val "1");] in
        let z_alt = [("z", Val "1"); ("z", Const "z")] in
        assert_equal
          true
          (List.mem (all_binding_alts s) z_alt ~equal:[%eq: Subst.t])
      );

    (* more_general *)

    "A variable is mapped to a constant">::(fun _ ->
        let s1 = [("x", Const "x")] in
        let s2 = [("x", Val "0")] in
        assert_equal true (more_general_subst [PUSH (Const "x")] s1 s2)
      );

    "A variable mapped to the same is mapped to different constants">::(fun _ ->
        let s1 = [("x", Const "x"); ("y", Const "x")] in
        let s2 = [("x", Val "0"); ("y", Val "1")] in
        assert_equal false (more_general_subst [PUSH (Const "x"); PUSH (Const "y")] s1 s2)
      );

    "Two substitutions are incomparable">::(fun _ ->
        let s1 = [("x", Const "x"); ("y", Val "0")] in
        let s2 = [("x", Val "0"); ("y", Const "y")] in
        assert_equal false (more_general_subst [PUSH (Const "x"); PUSH (Const "y")] s1 s2)
      );

    "More general is reflexive">::(fun _ ->
        let s1 = [("x", Const "x")] in
        assert_equal true (more_general_subst [PUSH (Const "x")] s1 s1)
      );

    "Different variables are mapped to the same">::(fun _ ->
        let s1 = [("x", Const "x"); ("y", Const "y")] in
        let s2 = [("x", Const "x"); ("y", Const "x")] in
        assert_equal true (more_general_subst [PUSH (Const "x"); PUSH (Const "y")] s1 s2)
      );

    "Same variables are mapped to a different variable">::(fun _ ->
        let s1 = [("x", Const "x"); ("y", Const "x")] in
        let s2 = [("x", Const "x"); ("y", Const "y")] in
        assert_equal false (more_general_subst [PUSH (Const "x"); PUSH (Const "y")] s1 s2)
      );

    (* less_general_subst *)

    "A variable is mapped to a constant">::(fun _ ->
        let s1 = [("x", Const "x")] in
        let s2 = [("x", Val "0")] in
        assert_equal false (less_general_subst [PUSH (Const "x")] s1 s2)
      );

    "A variable mapped to the same is mapped to different constants">::(fun _ ->
        let s1 = [("x", Const "x"); ("y", Const "x")] in
        let s2 = [("x", Val "0"); ("y", Val "1")] in
        assert_equal false (less_general_subst [PUSH (Const "x"); PUSH (Const "y")] s1 s2)
      );

    "Two substitutions are incomparable">::(fun _ ->
        let s1 = [("x", Const "x"); ("y", Val "0")] in
        let s2 = [("x", Val "0"); ("y", Const "y")] in
        assert_equal false (less_general_subst [PUSH (Const "x"); PUSH (Const "y")] s1 s2)
      );

    "More general is reflexive">::(fun _ ->
        let s1 = [("x", Const "x")] in
        assert_equal true (less_general_subst [PUSH (Const "x")] s1 s1)
      );

    "Different variables are mapped to the same">::(fun _ ->
        let s1 = [("x", Const "x"); ("y", Const "y")] in
        let s2 = [("x", Const "x"); ("y", Const "x")] in
        assert_equal false (less_general_subst [PUSH (Const "x"); PUSH (Const "y")] s1 s2)
      );

    "Same variables are mapped to a different variable">::(fun _ ->
        let s1 = [("x", Const "x"); ("y", Const "x")] in
        let s2 = [("x", Const "x"); ("y", Const "y")] in
        assert_equal true (less_general_subst [PUSH (Const "x"); PUSH (Const "y")] s1 s2)
      );

    (* rm_less_general *)

    "Do not remove incompatible">::(fun _ ->
        let s1 = [("x", Val "0"); ("y", Const "y")] in
        let s2 = [("x", Const "x"); ("y", Val "0")] in
        let t = [PUSH (Const "x"); PUSH (Const "y")] in
        assert_equal
          ~cmp:[%eq: Subst.t list]
          ~printer:[%show: Subst.t list]
          [s2] (rm_less_general t s1 [s2])
      );

    "Remove less general substition s2">::(fun _ ->
        let s1 = [("x", Val "0"); ("y", Const "y")] in
        let s2 = [("x", Val "0"); ("y", Val "0")] in
        let t = [PUSH (Const "x"); PUSH (Const "y")] in
        assert_equal
          ~cmp:[%eq: Subst.t list]
          ~printer:[%show: Subst.t list]
          [] (rm_less_general t s1 [s2])
      );

    "Remove less general substition s2 mapping to same variable">::(fun _ ->
        let s1 = [("x", Const "x"); ("y", Const "y")] in
        let s2 = [("x", Const "x"); ("y", Const "x")] in
        let t = [PUSH (Const "x"); PUSH (Const "y")] in
        assert_equal
          ~cmp:[%eq: Subst.t list]
          ~printer:[%show: Subst.t list]
          [] (rm_less_general t s1 [s2])
      );

    "Do not remove more general substition s2">::(fun _ ->
        let s1 = [("x", Val "0"); ("y", Const "y")] in
        let s2 = [("x", Const "x"); ("y", Const "x")] in
        let t = [PUSH (Const "x"); PUSH (Const "y")] in
        assert_equal
          ~cmp:[%eq: Subst.t list]
          ~printer:[%show: Subst.t list]
          [s2] (rm_less_general t s1 [s2])
      );

    (* rm_more_general *)

    "Do not remove incompatible">::(fun _ ->
        let s1 = [("x", Val "0"); ("y", Const "y")] in
        let s2 = [("x", Const "x"); ("y", Val "0")] in
        let t = [PUSH (Const "x"); PUSH (Const "y")] in
        assert_equal
          ~cmp:[%eq: Subst.t list]
          ~printer:[%show: Subst.t list]
          [s2] (rm_more_general t s1 [s2])
      );

    "Remove more general substition s1">::(fun _ ->
        let s1 = [("x", Val "0"); ("y", Const "y")] in
        let s2 = [("x", Val "0"); ("y", Val "0")] in
        let t = [PUSH (Const "x"); PUSH (Const "y")] in
        assert_equal
          ~cmp:[%eq: Subst.t list]
          ~printer:[%show: Subst.t list]
          [] (rm_more_general t s2 [s1])
      );

    "Remove more general substition s2 mapping to same variable">::(fun _ ->
        let s1 = [("x", Const "x"); ("y", Const "y")] in
        let s2 = [("x", Const "x"); ("y", Const "x")] in
        let t = [PUSH (Const "x"); PUSH (Const "y")] in
        assert_equal
          ~cmp:[%eq: Subst.t list]
          ~printer:[%show: Subst.t list]
          [] (rm_more_general t s2 [s1])
      );

    "Do not remove less general substition s2 mapping to same variable">::(fun _ ->
        let s1 = [("x", Const "x"); ("y", Const "y")] in
        let s2 = [("x", Const "x"); ("y", Const "x")] in
        let t = [PUSH (Const "y"); PUSH (Const "x")] in
        assert_equal
          ~cmp:[%eq: Subst.t list]
          ~printer:[%show: Subst.t list]
          [s2] (rm_more_general t s1 [s2])
      );

    "Do not remove less general substition s2">::(fun _ ->
        let s1 = [("x", Val "0"); ("y", Const "y")] in
        let s2 = [("x", Const "x"); ("y", Const "x")] in
        let t = [PUSH (Const "x"); PUSH (Const "y")] in
        assert_equal
          ~cmp:[%eq: Subst.t list]
          ~printer:[%show: Subst.t list]
          [s1] (rm_less_general t s2 [s1])
      );
  ]

let () =
  run_test_tt_main suite
