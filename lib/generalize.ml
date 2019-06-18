open Ebso
open Evmenc
open Z3util

let is_translation_valid s t =
  let c = enc_trans_val (mk_enc_consts s (`User [])) t in
  match solve_model [c] with
    | None -> true
    | Some _ -> false

let equiv = is_translation_valid

let rec drop_prefix s t = match s, t with
  | _ :: s', _ :: t' ->
    if equiv s' t'
    then drop_prefix s' t'
    else (s, t)
  | _ -> (s, t)

let rec drop_suffix s t = match List.rev s, List.rev t with
  | _ :: rs', _ :: rt' ->
    let s' = List.rev rs' and t' = List.rev rt' in
    if equiv s' t'
    then drop_suffix s' t'
    else (s, t)
  | _ -> (s, t)

let abstract_push_args _ _ = failwith "abstract_push_args not implemented"

let generalize _ _ = failwith "generalize not implemented"
