open Core
open Ebso
open Instruction

type t = Program.t * Program.t [@@deriving sexp, equal]

let pp fmt (pre, post) =
  Format.fprintf fmt "@[(%a, %a)@]" Program.pp_h pre Program.pp_h post

let show p = pp Format.str_formatter p |> Format.flush_str_formatter

let compare c1 c2 =
  let compare_instr i1 i2 = match (i1, i2) with
    | PUSH x, PUSH y -> Stackarg.compare x y
    | _, _ -> Instruction.compare i1 i2
  in
  Tuple.T2.compare
    ~cmp1:(List.compare compare_instr)
    ~cmp2:(List.compare compare_instr)
    c1 c2

let apply (pre, post) s = pre @ s @ post

let ext_prefix cs i = List.map cs ~f:(fun (pre, post) -> (i::pre, post))

let rec postfix s t = match (s, t) with
  | [], _ -> Some t
  | i1 :: s', i2:: t' when i1 = i2 -> postfix s' t'
  | _, _ -> None

let rec all_ctxts s t = match (s, t) with
  | _ :: _, i2 :: t' ->
    let cs = ext_prefix (all_ctxts s t') i2 in
    (match postfix s t with
     | Some post -> ([], post) :: cs
     | None -> cs)
  | [], [] -> [([], [])]
  | [], _  -> [([], t); (t, [])]
  | _, []  -> []
