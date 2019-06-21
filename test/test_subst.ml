open Core
open OUnit2
open Rule
open Ebso
open Stackarg
open Instruction
open Subst

let x = (Const "x")
let y = (Const "y")
let z = (Const "z")

let suite = "suite" >::: [

    (* is_mapped *)

    "Variable is mapped in substitution">::(fun _ ->
        assert_equal true (is_mapped x [(x, y)])
      );

    "Variable is not mapped in empty substitution">::(fun _ ->
        assert_equal false (is_mapped x [])
      );

    "Variable is not mapped in substitution">::(fun _ ->
        assert_equal false (is_mapped x [(z, y)])
      );

    (* map_exn *)

    "Map when exists in substitution">::(fun _ ->
        assert_equal
          ~cmp:[%eq: constarg] ~printer:[%show: constarg]
          "y" (map_exn x [(x, "y")])
      );

    (* map_extend *)

    "Extend empty substitution">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.tt] ~printer:[%show: Subst.t]
          [(x, y)] (map_extend x y [])
      );

    "Extend substitution">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t] ~printer:[%show: Subst.t]
          [(x, y); (z, Const "v")] (map_extend x y [(z, Const "v")])
      );

    "Element is mapped in extended substitution">::(fun _ ->
        let s = map_extend x "y" [] in
        assert_equal
          true (is_mapped x s)
      );

    (* update_Subst.t *)

    "Update substitution where same mapping exists">::(fun _ ->
        let s = [(x, y)] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some s) (update_var_subst x y s)
      );

    "Update substitution where different mapping exists">::(fun _ ->
        let s = [(x, y)] in
        let s' = map_extend z (Const "v") s in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some s') (update_var_subst z (Const "v") s)
      );

    "Fail when different mapping is inserted">::(fun _ ->
        let s = [(x, y)] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (update_var_subst x (Const "v") s)
      );

    "Fail when two different instructions are at same position">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (compute_var_subst [ADD] [MUL])
      );

    "Succeed on equal programs without PUSH">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some []) (compute_var_subst [ADD; SUB] [ADD; SUB])
      );

    "Fail on programs with different size">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (compute_var_subst [ADD; SUB] [ADD;])
      );

    "Succeed for PUSH with one argument">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some [(x, y)]) (compute_var_subst [PUSH x] [PUSH y;])
      );

    "Succeed for two PUSH with same arguments">::(fun _ ->
        let l1 = [PUSH x; PUSH (Const "x")] in
        let l2 = [PUSH y; PUSH (Const "y")] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some [(x, y)]) (compute_var_subst l1 l2)
      );

    "Succeed for two PUSH mapping arguments to same argument">::(fun _ ->
        let l1 = [PUSH x; PUSH y] in
        let l2 = [PUSH z; PUSH z] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some [(x, z); (y, z)]) (compute_var_subst l1 l2)
      );

    "Fail when two argument would need to map to different terms">::(fun _ ->
        let l1 = [PUSH x; PUSH x] in
        let l2 = [PUSH y; PUSH z] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (compute_var_subst l1 l2)
      );
 ]

let () =
  run_test_tt_main suite