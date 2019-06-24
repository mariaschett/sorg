open Core
open OUnit2
open Rule
open Rewrite_system

let suite = "suite" >::: [

    "Show system in TPDB format produces expected string" >:: (fun _ ->
        let rs =
          [ {lhs = [PUSH (Val "0"); PUSH (Const "x"); ADD]; rhs = [PUSH (Const "x")]}
          ; {lhs = [DUP I; SWAP I]; rhs = []}
          ]
        in
        assert_equal
          ~printer:Fn.id
          "(VAR x)\n\
           (RULES\n\
           \ \ PUSH(0, PUSH(x, ADD(P))) -> PUSH(x, P)\n\
           \ \ DUP1(SWAP1(P)) -> P\n\
           )"
          (show_tpdb rs)
      );
  ]

let () =
  run_test_tt_main suite
