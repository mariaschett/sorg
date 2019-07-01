open Core
open Ebso
open Instruction

type t = Program.t * Program.t [@@deriving show { with_path = false }, sexp, equal]

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

let add_postfix cs t = List.map cs ~f:(fun (pre, post) -> (pre, post @ t))

let rec all_ctxts s t = match (s, t) with
  | i1 :: _, i2 :: t' ->
    let cs = ext_prefix (all_ctxts s t') i2 in
    if i1 = i2 then (match postfix s t with
        | Some post -> add_postfix cs post
        | None -> cs
      )
      else cs
  | [], [] -> [([], [])]
  | [], _  -> [([], t); (t, [])]
  | _, []  -> []
