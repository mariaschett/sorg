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
          true (in_dom x s)
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

    (* map_to_val *)

    "No variable maps to value">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "1")] in
        assert_equal
          ~cmp:[%eq: vvar list] ~printer:[%show: vvar list]
          [] (map_to_val (Val "2") s)
      );

    "Only one variable maps to value">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "1")] in
        assert_equal
          ~cmp:[%eq: vvar list] ~printer:[%show: vvar list]
          ["y"] (map_to_val (Val "1") s)
      );

    "Two variables map to same">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "0")] in
        assert_equal
          ~cmp:(fun xs ys -> [%eq: vvar list]
                   (List.sort ~compare:compare_vvar xs)
                   (List.sort ~compare:compare_vvar ys))
          ~printer:[%show: vvar list]
          ["x"; "y"] (map_to_val (Val "0") s)
      );

    "Two variables map to same, one different">::(fun _ ->
        let s = [("x", Val "0"); ("y", Val "0"); ("z", Val "1");] in
        assert_equal
          ~cmp:(fun xs ys -> [%eq: vvar list]
                   (List.sort ~compare:compare_vvar xs)
                   (List.sort ~compare:compare_vvar ys))
          ~printer:[%show: vvar list]
          ["x"; "y"] (map_to_val (Val "0") s)
      );

    (* apply *)

    "Apply empty substitiution">::(fun _ ->
        let s = [] in
        let p = [PUSH (Const "x")] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          p (apply p s)
      );

    "Apply substitiution on variable in program">::(fun _ ->
        let s = [("x", Val "0")] in
        let p = [PUSH (Const "x")] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Val "0")] (apply p s)
      );

    "Apply substitiution where variable is not in program">::(fun _ ->
        let s = [("y", Val "0")] in
        let p = [PUSH (Const "x")] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          p (apply p s)
      );

    "Apply substitiution on program without PUSH">::(fun _ ->
        let s = [("x", Val "0")] in
        let p = [ADD] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          p (apply p s)
      );

    "Apply substitiution twice">::(fun _ ->
        let s = [("x", Val "0")] in
        let p = [PUSH (Const "x"); PUSH (Const "x")] in
        assert_equal
          ~cmp:[%eq: Program.t]
          ~printer:[%show: Program.t]
          [PUSH (Val "0"); PUSH (Val "0")] (apply p s)
      );
  ]

let () =
  run_test_tt_main suite
