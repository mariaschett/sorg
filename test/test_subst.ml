open OUnit2
open Ebso
open Stackarg
open Instruction
open Subst

let x = "x" and y = "y" and z = "z"
let x_v = Const x and y_v = Const y and z_v = Const z

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
          ~cmp:[%eq: vval] ~printer:[%show: vval]
          y_v (map_exn x [(x, y_v)])
      );

    (* map_extend *)

    "Extend empty substitution">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t] ~printer:[%show: Subst.t]
          [(x, y_v)] (map_extend x y_v [])
      );

    "Extend substitution">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t] ~printer:[%show: Subst.t]
          [(x, y_v); (z, Const "v")] (map_extend x y_v [(z, Const "v")])
      );

    "Element is mapped in extended substitution">::(fun _ ->
        let s = map_extend x "y" [] in
        assert_equal
          true (is_mapped x s)
      );

    (* update_Subst.t *)

    "Update substitution where same mapping exists">::(fun _ ->
        let s = [(x, y_v)] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some s) (update_subst x y_v s)
      );

    "Update substitution where different mapping exists">::(fun _ ->
        let s = [(x, y_v)] in
        let s' = map_extend z (Const "v") s in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some s') (update_subst z (Const "v") s)
      );

    "Fail when different mapping is inserted">::(fun _ ->
        let s = [(x, y_v)] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (update_subst x (Const "v") s)
      );

    "Fail when two different instructions are at same position">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (compute_subst [ADD] [MUL])
      );

    "Succeed on equal programs without PUSH">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some []) (compute_subst [ADD; SUB] [ADD; SUB])
      );

    "Fail on programs with different size">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (compute_subst [ADD; SUB] [ADD;])
      );

    "Succeed for PUSH with one argument">::(fun _ ->
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some [(x, y_v)]) (compute_subst [PUSH x_v] [PUSH y_v])
      );

    "Succeed for two PUSH with same arguments">::(fun _ ->
        let l1 = [PUSH x_v; PUSH x_v] in
        let l2 = [PUSH y_v; PUSH y_v] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some [(x, y_v)]) (compute_subst l1 l2)
      );

    "Succeed for two PUSH mapping arguments to same argument">::(fun _ ->
        let l1 = [PUSH x_v; PUSH y_v] in
        let l2 = [PUSH z_v; PUSH z_v] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some [(x, z_v); (y, z_v)]) (compute_subst l1 l2)
      );

    "Fail when two argument would need to map to different terms">::(fun _ ->
        let l1 = [PUSH x_v; PUSH x_v] in
        let l2 = [PUSH y_v; PUSH z_v] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          None (compute_subst l1 l2)
      );

    "Map PUSH argument to value">::(fun _ ->
        let l1 = [PUSH x_v] in
        let l2 = [PUSH (Val "0")] in
        assert_equal
          ~cmp:[%eq: Subst.t option] ~printer:[%show: Subst.t option]
          (Some [(x, Val "0")]) (compute_subst l1 l2)
      );
 ]

let () =
  run_test_tt_main suite
