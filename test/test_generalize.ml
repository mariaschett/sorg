open Core
open OUnit2
open Ebso
open Z3util
open Stackarg
open Instruction
open Evmenc
open Subst
open Rule
open Generalize

let s = [("x",Val "0"); ("y",Val "0"); ("z",Val "0"); ]

let ss =
  [("x",Val "0"); ("x",Const "y'"); ("x",Const "z'"); ("x",Const"x'");
   ("y",Val "0"); ("y",Const "z'"); ("y",Const "y'");
   ("z",Val "0"); ("z",Const "z'")]

let eq_enc_var ex ey =
  ex.x = ey.x && ex.v = ey.v &&
  (List.sort ~compare:compare_vval ex.eqv) = (List.sort ~compare:(compare_vval) ey.eqv)

let show_enc_var ex =
  "x = " ^ ex.x ^ "; v = " ^ [%show: vval] ex.v ^ "; forall = " ^ "; eqv = " ^
  [%show: vval list] (List.sort ~compare:compare_vval ex.eqv)

let sort_rules rs =
  let compare_instr i1 i2 = match (i1, i2) with
    | PUSH x, PUSH y -> Stackarg.compare x y
    | _, _ -> Instruction.compare i1 i2
  in
  let compare_rule r1 r2 = List.compare compare_instr (r1.lhs @ r1.rhs) (r2.lhs @ r2.rhs) in
  List.sort ~compare:compare_rule rs

let suite = "suite" >::: [

    (* mk_enc_var *)

    "Make encoding for x" >::(fun _ ->
        assert_equal
          ~cmp:eq_enc_var
          ~printer:show_enc_var
          {x = "x"; v = Val "0"; eqv = [Const "y'"; Const "z'"]}
          (mk_enc_var "x" s)
      );

      "Make encoding for y" >::(fun _ ->
          assert_equal
            ~cmp:eq_enc_var
            ~printer:show_enc_var
            {x = "y"; v = Val "0"; eqv = [Const "z'"]} (mk_enc_var "y" s)
      );

    "Make encoding for z" >::(fun _ ->
          assert_equal
            ~cmp:eq_enc_var
            ~printer:show_enc_var
            {x = "z"; v = Val "0";  eqv = []} (mk_enc_var "z" s)
      );

    (* proxy_assigns *)

    "Check assignments of proxyss">::(fun _ ->
        let m = List.map ss ~f:(fun (x,v) -> (proxy_name x v, (x,v))) in
        assert_equal
          ~cmp:(String.Map.equal [%eq: ventr])
          ~printer:(fun m -> String.Map.sexp_of_t sexp_of_ventr m |> Sexp.to_string)
        (String.Map.of_alist_exn m) (proxy_assigns (mk_enc_vars s))
      );

    (* enc_at_least_one_per_proxy *)

    "Check model for enc_at_least_one_per_proxy" >:: (fun _ ->
        let names = List.map ss ~f:(fun (x,v) -> (proxy_name x v)) in
        let m = solve_model_exn [enc_at_least_one_per_proxy (mk_enc_vars s)] in
        let trues =
          List.filter names
            ~f:(fun n -> Z3.Boolean.is_true @@ eval_const m (boolconst n))
        in
        assert_equal ~printer:[%show: int] ~cmp:[%eq: int]
          (List.length s)  (List.length trues)
      );

    (* enc_proxy_assigns *)

    "Check model for assigning proxys" >:: (fun _ ->
        let c = enc_proxy_assigns (mk_enc_vars s) in
        let c = c <&> conj @@ List.map ss ~f:(fun (x, v) -> boolconst (proxy_name x v)) in
        let m = solve_model_exn [c] in
        let vals =
          List.map s ~f:(fun (x, _) ->
              Z3.Arithmetic.Integer.get_int @@ eval_const m (seconst x))
        in
        assert_equal ~printer:[%show: int list] ~cmp:[%eq: int list]
          [0; 0; 0] vals
      );

    (* generalize *)

    "Find all generalizations" >:: (fun _ ->
        let r = {lhs = [PUSH (Val "0")]; rhs = [PUSH (Val "0")]} in
        let rs = generalize r in
        assert_equal
          ~printer:(fun rs -> [%show: Rule.t list] (sort_rules rs))
          ~cmp:(fun rs rs' -> [%eq: Rule.t list] (sort_rules rs) (sort_rules rs'))
          [{lhs = [PUSH (Const "x")]; rhs = [PUSH (Const "x")]}; r]
          rs
      );

    "Find all generalizations" >:: (fun _ ->
        let r = {lhs = [PUSH (Val "0"); PUSH (Val "0"); ADD]; rhs = [PUSH (Val "0")]} in
        let rs = generalize r in
        assert_equal
          ~printer:(fun rs -> [%show: Rule.t list] (sort_rules rs))
          ~cmp:(fun rs rs' -> [%eq: Rule.t list] (sort_rules rs) (sort_rules rs'))
          [ {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]}
          ; {lhs = [PUSH (Const "x"); PUSH (Val "0"); ADD]; rhs = [PUSH (Const "x")]}
          ; r
          ]
          rs
      );

  ]

let () =
  run_test_tt_main suite
