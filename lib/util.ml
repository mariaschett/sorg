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

let rec n_cartesian_product = function
| [] -> [[]]
| xs :: yys ->
    List.concat_map
      xs ~f:(fun x -> List.map (n_cartesian_product yys) ~f:(fun ys -> x :: ys))

let cartesian_product_up_to k m =
  let pair_of_list = function [i; j] -> (i,j) | _ -> failwith "List is not a pair." in
  let up_to i = List.init (i + 1) ~f:Fn.id in
  List.map (n_cartesian_product [up_to k; up_to m]) ~f:pair_of_list
