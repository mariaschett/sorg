open Ebso

type t =
  { lhs : Program.t;
    rhs : Program.t;
  }

(* careful, does not check alpha equvivalence *)
let equal r1 r2 = r1.lhs = r2.lhs && r1.rhs = r2.rhs

let pp fmt r = Format.fprintf fmt "@[%a -> %a@]" Program.pp_h r.lhs Program.pp_h r.rhs

let show r = pp Format.str_formatter r |> Format.flush_str_formatter
