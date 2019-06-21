open Core
open Ebso
open Subst

type t =
  { lhs : Program.t;
    rhs : Program.t;
  }

let alpha_equal p1 p2 = match (compute_var_subst p1 p2, compute_var_subst p2 p1) with
  | (Some _, Some _) -> true
  | _ -> false

let equal r1 r2 =
  alpha_equal (r1.lhs @ r1.rhs) (r2.lhs @ r2.rhs)

let pp fmt r = Format.fprintf fmt "@[%a -> %a@]" Program.pp_h r.lhs Program.pp_h r.rhs

let show r = pp Format.str_formatter r |> Format.flush_str_formatter
