open Core
open Ebso

type t = Program.t * Program.t [@@deriving show { with_path = false }, sexp, equal]

let apply (pre, post) s = pre @ s @ post
