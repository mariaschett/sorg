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
open Ebso
open Instruction.T
open Subst

type t = Ebso.Program.t [@@deriving sexp, equal, show]

let timeout = ref 0

let alpha_equal p1 p2 = match (match_opt p1 p2, match_opt p2 p1) with
  | (Some _, Some _) -> true
  | _ -> false

let compare s t =
  (* Ebso.Instruction ignores argument of PUSH for comparison *)
  let compare_instr i1 i2 = match (i1, i2) with
    | PUSH x, PUSH y -> Pusharg.compare x y
    | _, _ -> Instruction.compare i1 i2
  in
  List.compare compare_instr s t

let pp = Program.pp_h

let equiv =
  let is_translation_valid s t =
    (* candidate instruction set is irrelevant, hence [] *)
    let ecs = Enc_consts.mk_trans_val s t (`User []) in
    let c = Superoptimization.enc_trans_val ecs in
    match Z3util.solve_model_timeout [c] !timeout with
    | None -> true
    | Some _ -> false
  in is_translation_valid

let vars = Program.consts

let instruction_schema x = function
  | PUSH (Word (Val _)) -> Some (PUSH (Word (Const x)))
  | _ -> None

let maximal_schema c_0 =
  let fresh_var c = "w_" ^ Int.to_string c in
  List.fold_left ~init:(c_0, []) ~f:(fun (c, p) i ->
      match instruction_schema (fresh_var c) i with
      | Some i_a -> (c + 1, p @ [i_a])
      | None -> (c, p @ [i])
    )

(* print in tpdb format *)

let pp_tpdb fmt ?(var="P") p =
  let len = List.length p in
  let rec pp fmt = function
    | PUSH x :: is -> Format.fprintf fmt "%s%a%s%a" "PUSH(" Pusharg.pp x ", " pp is
    | i :: is -> Format.fprintf fmt "%a%s%a" Instruction.pp i "(" pp is
    | [] -> Format.fprintf fmt "%s%s" var (String.init len ~f:(fun _ -> ')'))
  in
  pp fmt p
