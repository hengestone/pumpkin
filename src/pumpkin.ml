type action = Tokens | Ast | Sast | Compile | CompileLua

let _ =
  if Array.length Sys.argv < 2 then
    print_string (
      "Usage: pmkn [required-option] <source file>\n" ^
        "required-option:\n" ^
        "\t-t: Prints token stream\n" ^
        "\t-a: Pretty prints Ast as a program\n" ^
        "\t-s: Prints Sast\n" ^
        "\t-c: Compiles to JavaScript\n"
    )
  else
    let action = List.assoc Sys.argv.(1) [ ("-t", Tokens);
                                           ("-a", Ast);
                                           ("-s", Sast);
                                           ("-c", Compile);
                                           ("-l", CompileLua);] and
    filename = Sys.argv.(2) in
    let file_in = open_in filename in
    try
      let lexbuf = Lexing.from_channel file_in in
      let token_list = Processor.get_token_list lexbuf in
      let program = Processor.parser token_list in
      let sast_output = Analyzer.annotate_program program in
      match action with
          Tokens ->
            print_string (Utils.token_list_to_string token_list)
        | Ast ->
            print_string (Utils.program_to_string program)
        | Sast ->
            print_string (Utils.a_program_to_string sast_output)
        | Compile ->
            print_string (Codegen.pumpkin_to_js sast_output ^ "\n")
        | CompileLua ->
            print_string (Codegen_lua.pumpkin_to_lua sast_output ^ "\n")

    with
        Exceptions.IllegalCharacter(c, ln) ->
          print_string
          (
            "In \"" ^ filename ^ "\", Illegal Character, '" ^
            Char.escaped c ^ "', line " ^ string_of_int ln ^ "\n"
          )
      | Exceptions.UnmatchedQuotation(ln) ->
          print_string("Unmatched Quotation, line " ^ string_of_int ln ^ "\n")
      | Exceptions.IndentationError(ln) ->
          print_string("Indentation Error, line " ^ string_of_int ln ^ "\n")
      | Parsing.Parse_error ->
          print_string
          (
            (
              if !Processor.last_token = Parser.INDENT then
                "Indentation Error"
              else
                "Syntax Error"
            ) ^ ", line " ^ string_of_int !Processor.line_number ^
            ", token " ^ Utils.token_to_string !Processor.last_token ^ "\n"
          )
