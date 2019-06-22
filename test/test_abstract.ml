open Core
open OUnit2
open Ebso
open Stackarg
open Abstract
open Subst

let s = [("x",Val "0"); ("y",Val "0"); ("z",Val "0"); ]

let eq_enc_var ex ey =
  ex.x = ey.x && ex.v = ey.v && ex.forall = ey.forall &&
  (List.sort ~compare:compare_vvar ex.eqv) = (List.sort ~compare:(compare_vvar) ey.eqv)

let show_enc_var ex =
  "x = " ^ ex.x ^ "; v = " ^ [%show: vval] ex.v ^ "; forall = " ^ ex.forall ^ "; eqv = " ^
  [%show: vvar list] (List.sort ~compare:compare_vvar ex.eqv)

let suite = "suite" >::: [

    (* mk_enc_var *)

    "Make encoding for x" >::(fun _ ->
        assert_equal
          ~cmp:eq_enc_var
          ~printer:show_enc_var
          {x = "x"; v = Val "0"; forall = "x'"; eqv = ["y"; "z"]}
          (mk_enc_var "x" s)
      );

      "Make encoding for y" >::(fun _ ->
          assert_equal
            ~cmp:eq_enc_var
            ~printer:show_enc_var
            {x = "y"; v = Val "0"; forall = "y'"; eqv = ["z"]} (mk_enc_var "y" s)
      );

    "Make encoding for z" >::(fun _ ->
          assert_equal
            ~cmp:eq_enc_var
            ~printer:show_enc_var
            {x = "z"; v = Val "0"; forall = "z'"; eqv = []} (mk_enc_var "z" s)
    );
  ]

let () =
  run_test_tt_main suite
