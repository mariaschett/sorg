open Ebso
open Evmenc
open Z3util

let is_translation_valid s t =
  let c = enc_trans_val (mk_enc_consts s (`User [])) t in
  match solve_model [c] with
    | None -> true
    | Some _ -> false

let equiv = is_translation_valid

let rec drop_prefix p1 p2 = match p1, p2 with
  | _ :: p1', _ :: p2' ->
    if equiv p1' p2'
    then drop_prefix p1' p2'
    else (p1, p2)
  | _ -> (p1, p2)

let generalize _ _ = failwith "generalize not implemented"
