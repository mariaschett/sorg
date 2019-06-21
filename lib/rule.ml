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

let consts r = List.stable_dedup (Program.consts r.lhs @ Program.consts r.rhs)

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

let pp_tpdb_system fmt ?(var="P") rs =
  let vars = List.stable_dedup (List.concat_map rs ~f:consts) in
  Format.fprintf fmt "@[<v>(VAR@[<hov>";
  List.iter vars ~f:(fun v -> Format.fprintf fmt "@ %s" v);
  Format.fprintf fmt "@])@,(RULES@,@[<v>";
  List.iter rs ~f:(fun r -> Format.fprintf fmt "  %a@," (pp_tpdb ~var:var) r);
  Format.fprintf fmt "@])@]"

let show_tpdb_system ?(var="P") rs =
  pp_tpdb_system Format.str_formatter ~var:var rs |> Format.flush_str_formatter
