open Core
open OUnit2

let suite = [
  "Generalize equal constant term" >::(fun _ ->
      let s = [DUP I] and let t = [DUP I]
      in
      assert_equal ~cmp:[%eq: Program.t pair list] ~printer:[%show: Program.t pair list]
          [(s, t)] (generalize s t)
    )
 ]

let () =
  run_test_tt_main suite
