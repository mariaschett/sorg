open Core
open Ebso
open Instruction
open Program_schema

type t =
  { lhs : Program_schema.t;
    rhs : Program_schema.t;
  }
[@@deriving sexp]

let equal r1 r2 =
  alpha_equal (r1.lhs @ r1.rhs) (r2.lhs @ r2.rhs)

let compare r1 r2 =
  let compare_instr i1 i2 = match (i1, i2) with
    | PUSH x, PUSH y -> Stackarg.compare x y
    | _, _ -> Instruction.compare i1 i2
  in
  if equal r1 r2 then 0 else
    List.compare compare_instr (r1.lhs @ r1.rhs) (r2.lhs @ r2.rhs)

let pp fmt r =
  Format.fprintf fmt "@[%a => %a@]" Program.pp_h r.lhs Program.pp_h r.rhs

let show r = pp Format.str_formatter r |> Format.flush_str_formatter

let consts r = List.stable_dedup (Program.consts r.lhs @ Program.consts r.rhs)

let maximal_rule_schema r =
  let (c_lhs, lhs_schema) = maximal_program_schema 0 r.lhs in
  let (_, rhs_schema) = maximal_program_schema c_lhs r.rhs in
  {lhs = lhs_schema; rhs = rhs_schema}

let match_opt gr sr =
  Subst.match_opt (gr.lhs @ gr.rhs) (sr.lhs @ sr.rhs)

let is_subrule r r' =
  let ctxts = Ctxt.all_ctxts r.lhs r'.lhs in
  List.exists ctxts ~f:(fun c -> Program.equal (Ctxt.apply c r.rhs) r'.rhs)

let pp_tpdb_program fmt ?(var="P") p =
  let len = List.length p in
  let rec pp fmt = function
    | PUSH x :: is -> Format.fprintf fmt "%s%a%s%a" "PUSH(" Stackarg.pp x ", " pp is
    | i :: is -> Format.fprintf fmt "%a%s%a" Instruction.pp i "(" pp is
    | [] -> Format.fprintf fmt "%s%s" var (String.init len ~f:(fun _ -> ')'))
  in
  pp fmt p

let pp_tpdb fmt ?(var="P") r =
  Format.fprintf fmt "@[<hov 2>%a ->@ %a@]"
    (pp_tpdb_program ~var:var) r.lhs
    (pp_tpdb_program ~var:var) r.rhs

let show_tpdb ?(var="P") r =
  pp_tpdb Format.str_formatter ~var:var r |> Format.flush_str_formatter
