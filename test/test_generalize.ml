open Generalize
open Ebso
open Instruction
open OUnit2

let suite = "suite" >::: [

  "Generalize equal constant term" >::(fun _ ->
      let s = [DUP I] and t = [DUP I]
      in
      assert_equal ~cmp:[%eq: (Program.t * Program.t) list] ~printer:[%show: (Program.t * Program.t) list]
          [(s, t)] (generalize s t)
    );

 ]

let () =
  run_test_tt_main suite
