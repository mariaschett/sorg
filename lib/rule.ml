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

type t =
  { lhs : Program_schema.t;
    rhs : Program_schema.t;
  } [@@deriving sexp]

let equal r1 r2 = Program_schema.alpha_equal (r1.lhs @ r1.rhs) (r2.lhs @ r2.rhs)

let compare r1 r2 =
  (* equal is alpha-equal here, that isn't the case for program_schemas *)
  if equal r1 r2
  then 0
  else Program_schema.compare (r1.lhs @ r1.rhs) (r2.lhs @ r2.rhs)

let pp fmt r =
  Format.fprintf fmt "@[%a => %a@]" Program_schema.pp r.lhs Program_schema.pp r.rhs

let show r = pp Format.str_formatter r |> Format.flush_str_formatter

let vars r = List.stable_dedup (Program_schema.vars r.lhs @ Program_schema.vars r.rhs)

let maximal_rule_schema r =
  let (c_lhs, lhs_schema) = Program_schema.maximal_schema 0 r.lhs in
  let (_, rhs_schema) = Program_schema.maximal_schema c_lhs r.rhs in
  {lhs = lhs_schema; rhs = rhs_schema}

let is_subrule r r' =
  let ctxts = Ctxt.all_ctxts r.lhs r'.lhs in
  List.exists ctxts ~f:(fun c -> Program_schema.equal (Ctxt.apply c r.rhs) r'.rhs)

(* print in tpdb format *)

let pp_tpdb fmt ?(var="P") r =
  Format.fprintf fmt "@[<hov 2>%a ->@ %a@]"
    (Program_schema.pp_tpdb ~var:var) r.lhs
    (Program_schema.pp_tpdb ~var:var) r.rhs

let show_tpdb ?(var="P") r =
  pp_tpdb Format.str_formatter ~var:var r |> Format.flush_str_formatter
