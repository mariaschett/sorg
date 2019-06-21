open Core
open Ebso
open Instruction
open Subst


type t =
  { lhs : Program.t;
    rhs : Program.t;
  }

let alpha_equal p1 p2 = match (compute_subst p1 p2, compute_subst p2 p1) with
  | (Some _, Some _) -> true
  | _ -> false

let equal r1 r2 =
  alpha_equal (r1.lhs @ r1.rhs) (r2.lhs @ r2.rhs)

let pp fmt r = Format.fprintf fmt "@[%a -> %a@]" Program.pp_h r.lhs Program.pp_h r.rhs

let show r = pp Format.str_formatter r |> Format.flush_str_formatter

let abstract_instruction w = function
  | PUSH (Val _) -> Some (PUSH (Const w))
  | _ -> None

let abstract_program c_0 =
  let fresh_var c = "w_" ^ Int.to_string c in
  List.fold_left ~init:(c_0, []) ~f:(fun (c, p) i ->
      match abstract_instruction (fresh_var c) i with
      | Some i_a -> (c + 1, p @ [i_a])
      | None -> (c, p @ [i])
    )

let abstract_rule r =
  let (c_lhs, lhs_a) = abstract_program 0 r.lhs in
  let (_, rhs_a) = abstract_program c_lhs r.rhs in
  {lhs = lhs_a; rhs = rhs_a}
