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
open Util

let sort_n_cartesian_product = List.sort ~compare:(List.compare Int.compare)
let comp_n_cartesian_product l1 l2 =
  (sort_n_cartesian_product l1) = (sort_n_cartesian_product l2)
let show_n_cartesian_product l =
  [%show: int list list] (sort_n_cartesian_product l)

let sort_2_cartesian_product = List.sort ~compare:(Tuple.T2.compare ~cmp1:Int.compare ~cmp2:Int.compare)
let comp_cartesian_product_up_to l1 l2 =
  (sort_2_cartesian_product l1) = (sort_2_cartesian_product l2)
let show_cartesian_product_up_to l =
  [%show: (int * int) list] (sort_2_cartesian_product l)

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

    (* cartesian_product_up_to *)

    "Cartesian product from {0} and {0}">::(fun _ ->
        assert_equal
          ~cmp:comp_cartesian_product_up_to
          ~printer:show_cartesian_product_up_to
          [(0,0)] (cartesian_product_up_to 0 0)
      );

    "Cartesian product from {0,1,2,3} and {0,1}">::(fun _ ->
        assert_equal
          ~cmp:comp_cartesian_product_up_to
          ~printer:show_cartesian_product_up_to
           [(0,0);(0,1);(1,0);(1,1);(2,0);(2,1);(3,0);(3,1)] (cartesian_product_up_to 3 1)
      );

  ]

let () =
  run_test_tt_main suite
