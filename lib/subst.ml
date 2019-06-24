open Core
open Ebso
open Instruction
open Stackarg

type vvar = constarg [@@deriving show { with_path = false }, sexp, compare, equal]
type vval = Stackarg.t [@@deriving show { with_path = false }, sexp, compare, equal]

type ventr = (vvar * vval) [@@deriving show { with_path = false }, sexp, compare, equal]
type t = ventr list [@@deriving show { with_path = false }, sexp, compare]

let equal s1 s2 = List.equal [%eq: ventr]
    (List.sort ~compare:[%compare: ventr] s1)
    (List.sort ~compare:[%compare: ventr] s2)

let dom s = List.map s ~f:Tuple.T2.get1

let in_dom x s = List.Assoc.mem s x ~equal:[%eq: vvar]

let map_exn x s = List.Assoc.find_exn s x ~equal:[%eq: vvar]

(* only extend if is_mapped x s is false *)
let map_extend x v s = List.Assoc.add s x v ~equal:[%eq: vvar]

let match_instruction s p1 p2 = match s, p1, p2 with
  | Some s', PUSH (Const x), PUSH w when not (in_dom x s') -> Some (map_extend x w s')
  | Some s', PUSH (Const x), PUSH w when (map_exn x s') = w -> s
  | Some _, i1, i2 when i1 = i2 -> s
  | _ -> None

let match_opt p1 p2 =
  let match_prefix = List.fold2 p1 p2 ~init:(Some []) ~f:match_instruction in
  match match_prefix with
  | Ok s -> s
  | Unequal_lengths -> None

let map_to_val v s =
  List.fold s ~init:[] ~f:(fun xs (x,v') -> if v = v' then x :: xs else xs)

let apply p s =
  let apply_instruction = function
    | PUSH (Const x) when in_dom x s -> PUSH (map_exn x s)
    | i -> i
  in
  List.map p ~f:(apply_instruction)
