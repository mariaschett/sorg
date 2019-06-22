open Core
open Ebso
open Instruction
open Evmenc
open Z3util
open Stackarg
open Rule
open Subst

(* to construct the constraints for a variable *)
type enc_var = {
  x : vvar;
  v : vval;
  forall : vvar;
  eqv : vvar list; (* contains only smaller variables *)
}

let mk_enc_var x s =
  let v = map_exn x s in
  { x = x;
    v = v;
    forall = x ^ "'";
    eqv = List.filter (map_to_val v s) ~f:(fun y -> x < y);
  }

let r = {lhs = [PUSH (Const "x"); PUSH (Const "y"); ADD]; rhs = [PUSH(Const "z")]}

let vs = Rule.consts r

let p_subst =
  [[("x",Val "0"); ("x",Const "y'"); ("x",Const "z'"); ("x",Const"x'")];
   [("y",Val "0"); ("y",Const "z'"); ("y",Const "y'");];
   [("z",Val "0"); ("z",Const "z'")]
  ]

let bool_name x y =
  let stackarg_print = function
    | Val n -> n
    | Const y -> y
    | Tmpl -> failwith "No Template variables allowed"
  in
  "l" ^ x ^ (stackarg_print y)

let z3_const = function
  | Val n -> senum_string n
  | Const y -> seconst y
  | Tmpl -> failwith "No Template variables allowed"

let const x c = seconst x <==> z3_const c
let abbrev x y = boolconst (bool_name x y) <->> (const x y)

let equiv p1 p2 =
  let open Z3Ops in
  let ea = mk_enc_consts p1 (`User []) in
  let sts = mk_state ea "_s" in
  let stt = mk_state ea "_t" in
  let kt = num (List.length p2) and ks = num (List.length ea.p) in
  ((List.foldi p2 ~init:(enc_program ea sts)
      ~f:(fun j enc oc -> enc <&> enc_instruction ea stt (num j) oc)) &&
       (* they start in the same state *)
   (enc_equivalence_at ea sts stt (num 0) (num 0)) &&
   sts.used_gas @@ (forall_vars ea @ [num 0]) ==
                   stt.used_gas @@ (forall_vars ea @ [num 0]) &&
   (* but their final state is different *)
   (enc_equivalence_at ea sts stt ks kt))

let literals ns =
  List.map ns ~f:(List.map ~f:(fun (x, v) -> boolconst (bool_name x v)))

let constr =
  (* forall vars *)
  foralls (List.map vs ~f:(fun x -> seconst (x ^ "'"))) (
    existss (List.map vs ~f:seconst) (
      conj (List.map (literals p_subst) ~f:disj) <&>
      (equiv r.lhs r.rhs)
      <&>
      conj (List.concat_map p_subst ~f:(List.map ~f:(Tuple.T2.uncurry abbrev)))
      <&>
      ~! (conj [boolconst "lx0"; boolconst "ly0"; boolconst "lz0"])
      <&>
      ~! (conj [boolconst "lx0"; boolconst "lyz'"; boolconst "lzz'"])
      <&>
      ~! (conj [boolconst "lxz'"; boolconst "ly0"; boolconst "lzz'"])
    )
  )
