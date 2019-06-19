open Core
open Ebso

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"sorg: A SuperOptimization based Rule Generator"
    [%map_open
      let i_s = flag "s" (required string)
          ~doc:"program to optimize"
      and
        i_t = flag "t" (required string)
          ~doc:"optimized program"
      and
        _ = flag "out" (optional string)
          ~doc:"filename write output to csv file"
      in
      fun () ->
        let lex = Sedlexing.Latin1.from_string in
        let (b_s, b_t) = (lex i_s, lex i_t) in
        let (s, t) = (Parser.parse b_s, Parser.parse b_t) in
         Out_channel.printf "%s" (([%show: Program.t] s) ^ "optimizes to \n" ^ ([%show: Program.t] t))
    ]
  |> Command.run ~version:"1.0"
