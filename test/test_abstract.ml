open Core
open OUnit2
open Ebso
open Z3util
open Stackarg
open Evmenc
open Subst
open Abstract

let s = [("x",Val "0"); ("y",Val "0"); ("z",Val "0"); ]

let ss =
  [("x",Val "0"); ("x",Const "y'"); ("x",Const "z'"); ("x",Const"x'");
   ("y",Val "0"); ("y",Const "z'"); ("y",Const "y'");
   ("z",Val "0"); ("z",Const "z'")]

let eq_enc_var ex ey =
  ex.x = ey.x && ex.v = ey.v && ex.forall = ey.forall &&
  (List.sort ~compare:compare_vval ex.eqv) = (List.sort ~compare:(compare_vval) ey.eqv)

let show_enc_var ex =
  "x = " ^ ex.x ^ "; v = " ^ [%show: vval] ex.v ^ "; forall = " ^ [%show: vval] ex.forall ^ "; eqv = " ^
  [%show: vval list] (List.sort ~compare:compare_vval ex.eqv)

let suite = "suite" >::: [

    (* mk_enc_var *)

    "Make encoding for x" >::(fun _ ->
        assert_equal
          ~cmp:eq_enc_var
          ~printer:show_enc_var
          {x = "x"; v = Val "0"; forall = Const "x'"; eqv = [Const "y'"; Const "z'"]}
          (mk_enc_var "x" s)
      );

      "Make encoding for y" >::(fun _ ->
          assert_equal
            ~cmp:eq_enc_var
            ~printer:show_enc_var
            {x = "y"; v = Val "0"; forall = Const "y'"; eqv = [Const "z'"]} (mk_enc_var "y" s)
      );

    "Make encoding for z" >::(fun _ ->
          assert_equal
            ~cmp:eq_enc_var
            ~printer:show_enc_var
            {x = "z"; v = Val "0"; forall = Const "z'"; eqv = []} (mk_enc_var "z" s)
      );

    (* enc_literal_map *)

    "Check map of encoding literals">::(fun _ ->
        let m = List.map ss ~f:(fun (x,v) -> (literal_name x v, (x,v))) in
        assert_equal
          ~cmp:(String.Map.equal [%eq: ventr])
          ~printer:(fun m -> String.Map.sexp_of_t sexp_of_ventr m |> Sexp.to_string)
        (String.Map.of_alist_exn m) (enc_literals_map (mk_enc_vars s))
      );

    (* enc_literals_atleastone *)

    "Check model for enc_literals_atleastone" >:: (fun _ ->
        let names = List.map ss ~f:(fun (x,v) -> (literal_name x v)) in
        let m = solve_model_exn [enc_literals_atleastone (mk_enc_vars s)] in
        let trues =
          List.filter names
            ~f:(fun n -> Z3.Boolean.is_true @@ eval_const m (boolconst n))
        in
        assert_equal ~printer:[%show: int] ~cmp:[%eq: int]
          (List.length s)  (List.length trues)
      );

    (* enc_literals_def *)

    "Check model for defining literals" >:: (fun _ ->
        let c = enc_literals_def (mk_enc_vars s) in
        let c = c <&> conj @@ List.map ss ~f:(fun (x, v) -> boolconst (literal_name x v)) in
        let m = solve_model_exn [c] in
        let vals =
          List.map s ~f:(fun (x, _) ->
              Z3.Arithmetic.Integer.get_int @@ eval_const m (seconst x))
        in
        assert_equal ~printer:[%show: int list] ~cmp:[%eq: int list]
          [0; 0; 0] vals
      );

  ]

let () =
  run_test_tt_main suite
