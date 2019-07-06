open Core
open Ebso
open Instruction
open Subst

type t = Ebso.Program.t [@@deriving sexp, equal, show]

let timeout = ref 0

let alpha_equal p1 p2 = match (match_opt p1 p2, match_opt p2 p1) with
  | (Some _, Some _) -> true
  | _ -> false

let equiv =
  let is_translation_valid s t =
    (* candidate instruction set is irrelevant, hence [] *)
    let ecs = Evmenc.mk_enc_consts s (`User []) in
    let c = Evmenc.enc_trans_val ecs t in
    match Z3util.solve_model_timeout [c] !timeout with
    | None -> true
    | Some _ -> false
  in is_translation_valid

let instruction_schema x = function
  | PUSH (Val _) -> Some (PUSH (Const x))
  | _ -> None

let maximal_schema c_0 =
  let fresh_var c = "w_" ^ Int.to_string c in
  List.fold_left ~init:(c_0, []) ~f:(fun (c, p) i ->
      match instruction_schema (fresh_var c) i with
      | Some i_a -> (c + 1, p @ [i_a])
      | None -> (c, p @ [i])
    )

let pp_tpdb fmt ?(var="P") p =
  let len = List.length p in
  let rec pp fmt = function
    | PUSH x :: is -> Format.fprintf fmt "%s%a%s%a" "PUSH(" Stackarg.pp x ", " pp is
    | i :: is -> Format.fprintf fmt "%a%s%a" Instruction.pp i "(" pp is
    | [] -> Format.fprintf fmt "%s%s" var (String.init len ~f:(fun _ -> ')'))
  in
  pp fmt p
