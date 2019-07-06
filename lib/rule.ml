open Core
open Ebso
open Program_schema

type t =
  { lhs : Program_schema.t;
    rhs : Program_schema.t;
  } [@@deriving sexp]

let equal r1 r2 = alpha_equal (r1.lhs @ r1.rhs) (r2.lhs @ r2.rhs)

let compare r1 r2 =
  (* equal is alpha-equal here, that isn't the case for program_schemas *)
  if equal r1 r2
  then 0
  else Program_schema.compare (r1.lhs @ r1.rhs) (r2.lhs @ r2.rhs)

let pp fmt r =
  Format.fprintf fmt "@[%a => %a@]" Program_schema.pp r.lhs Program_schema.pp r.rhs

let show r = pp Format.str_formatter r |> Format.flush_str_formatter

let consts r = List.stable_dedup (Program.consts r.lhs @ Program.consts r.rhs)

let maximal_rule_schema r =
  let (c_lhs, lhs_schema) = maximal_schema 0 r.lhs in
  let (_, rhs_schema) = maximal_schema c_lhs r.rhs in
  {lhs = lhs_schema; rhs = rhs_schema}

let is_subrule r r' =
  let ctxts = Ctxt.all_ctxts r.lhs r'.lhs in
  List.exists ctxts ~f:(fun c -> Program.equal (Ctxt.apply c r.rhs) r'.rhs)

let pp_tpdb fmt ?(var="P") r =
  Format.fprintf fmt "@[<hov 2>%a ->@ %a@]"
    (Program_schema.pp_tpdb ~var:var) r.lhs
    (Program_schema.pp_tpdb ~var:var) r.rhs

let show_tpdb ?(var="P") r =
  pp_tpdb Format.str_formatter ~var:var r |> Format.flush_str_formatter
