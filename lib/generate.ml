open Ebso
open Evmenc
open Z3util

let is_translation_valid s t =
  let c = enc_trans_val (mk_enc_consts s (`User [])) t in
  match solve_model [c] with
    | None -> true
    | Some _ -> false

let equiv = is_translation_valid

let rec strip_prefix s t = match s, t with
  | _ :: s', _ :: t' ->
    if equiv s' t'
    then strip_prefix s' t'
    else (s, t)
  | _ -> (s, t)

let rec strip_suffix s t = match List.rev s, List.rev t with
  | _ :: rs', _ :: rt' ->
    let s' = List.rev rs' and t' = List.rev rt' in
    if equiv s' t'
    then strip_suffix s' t'
    else (s, t)
  | _ -> (s, t)

let generate_rules _ _ = failwith "generate_rules not implemented"
