open Core
open Ebso
open Stackarg
open Instruction

type var_subst = (constarg * constarg) list [@@deriving show { with_path = false }, sexp]

let equal_var_subst s1 s2 = List.equal ~equal:[%eq: constarg * constarg]
    (List.sort ~compare:[%compare: constarg * constarg] s1)
    (List.sort ~compare:[%compare: constarg * constarg] s2)

let is_mapped a s = List.Assoc.mem s a ~equal:[%eq: constarg]

let map_exn a s = List.Assoc.find_exn s a ~equal:[%eq: constarg]

(* only extend if is_mapped a1 s is false *)
let map_extend a1 a2 s = List.Assoc.add s a1 a2 ~equal:[%eq: constarg]

let update_var_subst a1 a2 s =
  if not (is_mapped a1 s)
  then Some (map_extend a1 a2 s)
  else if (map_exn a1 s) = a2 then (Some s) else None

let compute_var_subst p1 p2 =
  let rec compute_subst' p1 p2 s = match p1, p2 with
    | [], [] -> Some s
    | PUSH (Const a1) :: t1, PUSH (Const a2) :: t2 ->
      Option.(update_var_subst a1 a2 s >>= compute_subst' t1 t2)
    | i1 :: t1, i2 :: t2 when i1 = i2 -> compute_subst' t1 t2 s
    | _ -> None
  in compute_subst' p1 p2 []

let alpha_equal p1 p2 = match (compute_var_subst p1 p2, compute_var_subst p2 p1) with
  | (Some _, Some _) -> true
  | _ -> false

type t =
  { lhs : Program.t;
    rhs : Program.t;
  }

let equal r1 r2 =
  alpha_equal (r1.lhs @ r1.rhs) (r2.lhs @ r2.rhs)

let pp fmt r = Format.fprintf fmt "@[%a -> %a@]" Program.pp_h r.lhs Program.pp_h r.rhs

let show r = pp Format.str_formatter r |> Format.flush_str_formatter
