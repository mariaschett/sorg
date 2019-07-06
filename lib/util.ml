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
