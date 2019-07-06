open Core
open OUnit2
open Util

let comp_n_cartesian_product l1 l2 =
  let sort_n_cartesian_product = List.sort ~compare:(List.compare Int.compare) in
  (sort_n_cartesian_product l1) = (sort_n_cartesian_product l2)

let show_n_cartesian_product l =
  let sort_n_cartesian_product = List.sort ~compare:(List.compare Int.compare) in
  [%show: int list list] (sort_n_cartesian_product l)

let suite = "suite" >::: [

    (* cartesian product *)

    "Single lists to n_cartesian products">::(fun _ ->
        assert_equal
          ~cmp:comp_n_cartesian_product
          ~printer:show_n_cartesian_product
          [[1;2;3]] (n_cartesian_product [[1];[2];[3]])
      );

    "One list with two elements to n_cartesian products">::(fun _ ->
        assert_equal
          ~cmp:comp_n_cartesian_product
          ~printer:show_n_cartesian_product
          [[1;2;3]; [1;2;4]] (n_cartesian_product [[1];[2];[3;4]])
      );

    "Two list with two elements to n_cartesian products">::(fun _ ->
        assert_equal
          ~cmp:comp_n_cartesian_product
          ~printer:show_n_cartesian_product
          [[1;2;3]; [1;2;4]; [1;5;3]; [1;5;4];] (n_cartesian_product [[1];[2;5];[3;4]])
      );
  ]

let () =
  run_test_tt_main suite
