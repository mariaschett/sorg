open Core

let rec n_cartesian_product = function
| [] -> [[]]
| xs :: yys ->
    List.concat_map
      xs ~f:(fun x -> List.map (n_cartesian_product yys) ~f:(fun ys -> x :: ys))
