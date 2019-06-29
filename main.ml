open Core
open Ebso

let header =
  [ "source bytecode"
  ; "target bytecode"
  ; "target opcode"
  ; "target instruction count"
  ; "source gas"
  ; "target gas"
  ; "gas saved"
  ; "known optimal"
  ; "translation validation"
  ]

let row_to_optimization r =
  let parse s = Parser.parse @@ Sedlexing.Latin1.from_string s in
  let sbc = Csv.Row.find r "source bytecode"
  and tbc = Csv.Row.find r "target bytecode"
  and tv = Csv.Row.find r "translation validation"
  and gs = Csv.Row.find r "gas saved" in
  if String.equal gs "0" || String.equal tv "false" then None
  else Some (parse sbc, parse tbc)

let process_optimization (rs, muls) (s, t) =
  let rs' = Generate.generate_rules s t in
  let muls' = if Rewrite_system.size rs' > 1 then ((s, t), rs') :: muls else muls in
  Out_channel.printf "%s"
     (Rewrite_system.show rs');
  Out_channel.flush stdout;
  (rs' @ rs, muls')

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"sorg: A SuperOptimization based Rule Generator"
    [%map_open
      let in_csv = flag "incsv" (optional string)
          ~doc:"csv read optimizations from csv"
      and  _ = flag "out" (optional string)
          ~doc:"filename write output to csv file"
      and opt = anon (maybe (t2 ("LHS" %: string) ("RHS" %: string)))
      in
      fun () ->
        let rs =
          match in_csv with
          | Some file ->
            let csv = Csv.Rows.load ~has_header:true ~header:header file in
            List.filter_map csv ~f:row_to_optimization
          | None ->
            match opt with
            | Some (lhs, rhs) ->
              let parse s = Parser.parse @@ Sedlexing.Latin1.from_string s in
              [(parse lhs, parse rhs)]
            | None -> []
        in
        Evmenc.set_wsz 256;
        List.fold rs ~init:([], []) ~f:(process_optimization) |> ignore
    ]
  |> Command.run ~version:"1.0"
