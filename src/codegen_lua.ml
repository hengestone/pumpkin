open Ast
open Sast
open Exceptions

let rec strip_semicolon l =
  match l with
      [] -> ' '::[]
    | (hd::tl) -> if (hd = ';') then strip_semicolon tl else hd::(strip_semicolon tl)

let explode s =
  let rec exp i l =
    if i < 0 then l
    else exp(i - 1)(s.[i] :: l) in
      exp(String.length s - 1)[]

let implode l =
  let res = String.create(List.length l) in
  let rec imp i = function
      [] -> res
    | c :: l -> res.[i] <-c; imp(i + 1) l in
      imp 0 l


let flip_last = fun l ->
  let r = List.rev l
  in (List.hd r) :: (List.rev (List.tl r))

let sanitize str =
  implode ( strip_semicolon ( explode ( str) ) )

let type_list = function
      List(_) -> true
    | _ -> false

let reserve_mismatch = function
      AListLiteral(_, _) -> false
    | AIdLiteral(id, t) when (type_list t) -> false
    | _ -> true

let operation_to_string = function
    Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Divide -> "/"
  | Modulo -> "%"
  | Eq -> "=="
  | Neq -> "~="
  | Gt -> ">"
  | Lt -> "<"
  | Gte -> ">="
  | Lte -> "<="
  | And -> "and"
  | Or -> "or"
  | Not -> "~"

let param_to_lua (id, t) = id

let param_to_type (id, t) = t

let rec returns_unit = function
    Unit -> true
  | Function(_, ret) -> returns_unit ret
  | _ -> false


let is_partial = function
    Function(_, _) -> true
  | _ -> false

let is_IfElseBlock = function
    AIfElseBlock(_,_,_,_) -> true
  | _ -> false

let get_IfElseExprList(n, expr) =
  match expr with
      AIfElseBlock(_,if_expr, else_expr, _) ->
        if n = 0 then if_expr else else_expr
    | _ -> []

let get_IfElseE = function
      AIfElseBlock(e, _, _, _) -> e
    | _ -> AUnitLiteral

let rec aexpression_to_lua lines =
  let rec build_return = function
     [] -> "\n\t"
  |  [single] -> "\n\treturn " ^ (aexpression_to_lua single)
  |  hd::tl -> "\n\t" ^ (aexpression_to_lua hd) ^ (build_return tl)
  in
  match lines with
    AIntLiteral(i) -> string_of_int(i)
  | AFloatLiteral(f) -> string_of_float(f)
  | ABinop(e1, op, e2, t) ->
      if op = Cons then
        "__cons__(" ^
        sanitize(aexpression_to_lua e1) ^ "," ^
        sanitize(aexpression_to_lua e2) ^ ")"
      else
        "(" ^ sanitize(aexpression_to_lua e1) ^ " " ^
        operation_to_string op ^ " " ^
        sanitize(aexpression_to_lua e2) ^ ")"
  | AUnop(op, e1, t) ->
     "(" ^  operation_to_string(op) ^ " " ^
      aexpression_to_lua(e1) ^ ")3"
      (* Unops won't be bythemselves as a single expression
       * so no semicolon *)
  | ABoolLiteral(b) ->
      if b then "true"
      else "false"
  | AStringLiteral(s) -> s
  | ACharLiteral(c) -> "'" ^ Char.escaped c ^ "'"
  | AUnitLiteral -> "nil"
  | AIdLiteral(id, t) -> id
  | AAssign(id, e, t) ->
      "local" ^ " " ^ id ^ " = " ^
      aexpression_to_lua e
  | AReassign(id, e, t) ->
      id ^ " = " ^ aexpression_to_lua e
  | AMapLiteral(map_list, t) ->
      let map_expression_tupal_to_string (e1, e2) =
        (aexpression_to_lua e1) ^ "= " ^ (aexpression_to_lua e2)
      in "{" ^
      sanitize(String.concat ", " (List.map map_expression_tupal_to_string
      map_list)) ^ "}"
  | AMapAccess(id, param, s_type) ->
      aexpression_to_lua id ^ "{" ^ aexpression_to_lua param ^ "}"
  | ATupleLiteral(e_list, t) ->
      "{" ^ String.concat ", " (List.map aexpression_to_lua e_list) ^ "}"
  | AListLiteral(e_list, t) ->
      "{" ^ String.concat ", " (List.map aexpression_to_lua e_list) ^ "}"
  | ATupleAccess(id, indx, t) ->
      sanitize(aexpression_to_lua id) ^ "[" ^ sanitize(aexpression_to_lua indx) ^ "]"
  | AListAccess(id, indx, t) ->
      sanitize(aexpression_to_lua id) ^ "[" ^ sanitize(aexpression_to_lua indx) ^ "]"

  | AIfBlock(e, e_list, _) ->
      "\nif " ^ sanitize(aexpression_to_lua e) ^ " then" ^
      "\n" ^ String.concat "\n\t" (List.map aexpression_to_lua e_list) ^
      "\nend\n"
  | AIfElseBlock(e, e_list1, e_list2, _) ->
      "\nif " ^ sanitize(aexpression_to_lua e) ^ " then" ^
      "\n\t" ^ String.concat "\n\t" (List.map aexpression_to_lua e_list1) ^
      "\n" ^
      "else" ^
      "\n\t" ^ String.concat "\n\t" (List.map aexpression_to_lua e_list2) ^
      "\nend\n"
  | AFuncDecl(id, p_list, e_list, t) ->
      if returns_unit t then
        if param_to_type(List.hd p_list) <> Unit then
          "local function " ^ id ^ "(" ^
          String.concat ", " (List.map param_to_lua p_list) ^ ")" ^
          " \n" ^ String.concat "\n\t" (List.map aexpression_to_lua e_list) ^
          "\nend\n"
        else
         "local function " ^ id ^ "()" ^
         "\n" ^ String.concat "\n\t" (List.map aexpression_to_lua e_list) ^
         "\nend\n"
      else
        if param_to_type(List.hd p_list) <> Unit then
          let flipped_list = flip_last e_list in
            "local function " ^ id ^ "(" ^
            (String.concat ", " (List.map param_to_lua p_list)) ^
            ")" ^
            (String.concat "\n\t" (List.map aexpression_to_lua (List.tl flipped_list))) ^
            (if is_IfElseBlock(List.hd flipped_list) then
              "\nif (" ^
              sanitize(aexpression_to_lua(get_IfElseE (List.hd flipped_list))) ^
              ") then" ^
              (build_return (get_IfElseExprList(0, (List.hd flipped_list)))) ^
              "\nelse" ^
              (build_return (get_IfElseExprList(1, (List.hd flipped_list)))) ^
              "\nend\n"
             else
               "\n\treturn " ^
              (aexpression_to_lua (List.hd flipped_list))) ^
            "\nend\n"
        else
          let flipped_list = flip_last e_list in
            "local function ()" ^
            (String.concat "\n\t" (List.map aexpression_to_lua (List.tl flipped_list))) ^
            (if is_IfElseBlock(List.hd flipped_list) then
              "\nif (" ^
              sanitize(aexpression_to_lua(get_IfElseE (List.hd flipped_list))) ^
              ")" ^
              (build_return (get_IfElseExprList(0, (List.hd flipped_list)))) ^
              "\nelse" ^
              (build_return (get_IfElseExprList(1, (List.hd flipped_list)))) ^
              "end\n"
             else
               "\n\treturn " ^
              (aexpression_to_lua (List.hd flipped_list))) ^
            "\nend\n"

  | AFuncAnon(p_list, exp, t) ->
      if returns_unit t then
        if param_to_type(List.hd p_list) <> Unit then
          "function(" ^
          String.concat ", " (List.map param_to_lua p_list) ^ ")" ^
          "\n\t" ^ aexpression_to_lua exp ^
          "\nend\n"
        else
         "function()" ^
         "\n\t" ^ aexpression_to_lua exp ^
         "\nend\n"
      else
        if param_to_type(List.hd p_list) <> Unit then
          "function(" ^
          String.concat ", " (List.map param_to_lua p_list) ^ ")" ^
          "\n\treturn " ^ aexpression_to_lua exp ^
          "\nend\n"
        else
          "function()" ^
          "\n\treturn " ^ aexpression_to_lua exp ^
          "\nend\n"
  | AFuncCall(id, params, s_type) ->
      if (s_type = Reserved && ((List.length params <> 1) || ( reserve_mismatch(List.hd params)))) then
        raise(ReservedFuncTypeMisMatch)
      else if s_type = Print then
        "print(" ^ sanitize(aexpression_to_lua (List.hd params)) ^ ")"
      else
        if List.hd params <> AUnitLiteral then
          if is_partial s_type then
            aexpression_to_lua id ^ "(" ^
            sanitize(String.concat ", " (List.map aexpression_to_lua (List.rev params)))
          else
            aexpression_to_lua id ^ "(" ^
            sanitize(String.concat ", " (List.map aexpression_to_lua (List.rev params))) ^
            ")"
        else
          aexpression_to_lua id ^ ")"
  | AFuncPiping(exp1, exp2, t) ->
      sanitize(aexpression_to_lua exp2) ^ ", " ^ sanitize(aexpression_to_lua exp1) ^ ")"
     (* sanitize(aexpression_to_lua exp2) ^ "(" ^ sanitize(aexpression_to_lua exp1) ^ ")" *)
  | AFuncComposition(exp1, exp2, t) ->
      "__compose__(" ^ sanitize(aexpression_to_lua exp2) ^ ", " ^
      sanitize(aexpression_to_lua exp1) ^ ")"

let pumpkin_to_lua a_expressions =
  "
    local table = table
    local unpack = unpack

    local function __compose__(...)
      local funcs = arg
      return function(...)
        local args = arg
        for i=#funcs, 1, -1 do
          args = {funcs[i](args)}
        end
        return args[1]
      end
    end

    local function __cons__(elem, lst)
      local temp = {elem}
      for i = 1,#lst do
        table.insert(temp, lst[i])
      end
      return temp
    end

    -- returns the head element of the table
    local function hd(...)
      if #arg > 0 then
        return arg[1][1]
      else
        return nil
      end
    end

    -- returns the table with its head element removed
    local function tl(...)
      if #arg > 0 then
        local temp = {unpack(arg[1])}
        table.remove(temp, 1)
        return temp
      else
        return {}
      end
    end

    local function len(lst)
      return #lst
    end

    local function is_empty(lst)
      return #lst == 0
    end

      \n" ^
  String.concat "\n" (List.map aexpression_to_lua a_expressions)


