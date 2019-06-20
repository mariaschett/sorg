open Core
open Ebso
open Instruction
open Evmenc
open Z3util

let p1 = [PUSH (Const "x"); PUSH (Const "y"); ADD] and p2 = [PUSH(Const "z")]

let vs = ["x"; "y"; "z"]

let const x c = seconst x <==> senum c
let var x y = seconst x <==> seconst y
let abbrev_c x y = boolconst ("l" ^ x ^ Int.to_string y) <==> (const x y)
let abbrev_v x y = boolconst ("l" ^ x ^ y) <==> (var x y)

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


let constr =
  (* forall vars *)
  foralls (List.map vs ~f:(fun x -> seconst (x ^ "'"))) (
    existss (List.map vs ~f:seconst) (
      conj [disj [const "x" 0; var "x" "y"; var "x" "z"; var "x" "x'"];
            disj [const "y" 0; var "y" "z"; var "y" "y'"];
            disj [const "z" 0; var "z" "z'"]
           ] <&>
      (equiv p1 p2)
      <&>
      conj [
        abbrev_c "x" 0; abbrev_v "x" "y"; abbrev_v "x" "z";
        abbrev_c "y" 0; abbrev_v "y" "z";
        abbrev_c "z" 0;
      ] <&>
      ~! (conj [boolconst "lx0"; boolconst "ly0"; boolconst "lz0"])
    )
  )
