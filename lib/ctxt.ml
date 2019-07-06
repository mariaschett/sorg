open Core
open Ebso
open Instruction

exception Not_enough_context

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

let strip_ctxt i j t =
  if i + j <= List.length t
  then List.sub ~pos:i ~len:(List.length t - i - j) t
  else raise Not_enough_context

let rec common_prefix ss ts = match ss, ts with
  | s :: ss', t :: ts' when s = t -> s :: (common_prefix ss' ts')
  | _, _ -> []

let common_postfix ss ts =
  List.rev (common_prefix (List.rev ss) (List.rev ts))
