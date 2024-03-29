// Implementation file for parser generated by fsyacc
module LangParser
#nowarn "64";; // turn off warnings that type variables used in production annotations are instantiated to concrete type
open Microsoft.FSharp.Text.Lexing
open Microsoft.FSharp.Text.Parsing.ParseHelpers
# 4 "LangParser.fsp"

open System
open Lang
let currentLabel = ref 1
let labelCmd() =
   let tmp = !currentLabel
   incr currentLabel
   tmp
let getLabel():int =
   let l = !currentLabel
   l-1

# 19 "LangParser.fs"
// This type is the type of tokens accepted by the parser
type token = 
  | EOF
  | ABORT
  | READ
  | WRITE
  | TRUE
  | FALSE
  | OD
  | FI
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | GUARD
  | MODULE
  | END
  | SEMICOLON
  | ARROW
  | SKIP
  | OR
  | AND
  | ADD
  | DIV
  | MUL
  | NOT
  | MINUS
  | EQ
  | LTN
  | GTN
  | NEQ
  | LEQ
  | GEQ
  | DO
  | IF
  | ASGN
  | COLON
  | NUMBER of (int)
  | ID of (string)
// This type is used to give symbolic names to token indexes, useful for error messages
type tokenId = 
    | TOKEN_EOF
    | TOKEN_ABORT
    | TOKEN_READ
    | TOKEN_WRITE
    | TOKEN_TRUE
    | TOKEN_FALSE
    | TOKEN_OD
    | TOKEN_FI
    | TOKEN_LPAREN
    | TOKEN_RPAREN
    | TOKEN_LBRACK
    | TOKEN_RBRACK
    | TOKEN_GUARD
    | TOKEN_MODULE
    | TOKEN_END
    | TOKEN_SEMICOLON
    | TOKEN_ARROW
    | TOKEN_SKIP
    | TOKEN_OR
    | TOKEN_AND
    | TOKEN_ADD
    | TOKEN_DIV
    | TOKEN_MUL
    | TOKEN_NOT
    | TOKEN_MINUS
    | TOKEN_EQ
    | TOKEN_LTN
    | TOKEN_GTN
    | TOKEN_NEQ
    | TOKEN_LEQ
    | TOKEN_GEQ
    | TOKEN_DO
    | TOKEN_IF
    | TOKEN_ASGN
    | TOKEN_COLON
    | TOKEN_NUMBER
    | TOKEN_ID
    | TOKEN_end_of_input
    | TOKEN_error
// This type is used to give symbolic names to token indexes, useful for error messages
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_LangProgram
    | NONTERM_Command
    | NONTERM_GCmd
    | NONTERM_Arrow
    | NONTERM_Expression

// This function maps tokens to integers indexes
let tagOfToken (t:token) = 
  match t with
  | EOF  -> 0 
  | ABORT  -> 1 
  | READ  -> 2 
  | WRITE  -> 3 
  | TRUE  -> 4 
  | FALSE  -> 5 
  | OD  -> 6 
  | FI  -> 7 
  | LPAREN  -> 8 
  | RPAREN  -> 9 
  | LBRACK  -> 10 
  | RBRACK  -> 11 
  | GUARD  -> 12 
  | MODULE  -> 13 
  | END  -> 14 
  | SEMICOLON  -> 15 
  | ARROW  -> 16 
  | SKIP  -> 17 
  | OR  -> 18 
  | AND  -> 19 
  | ADD  -> 20 
  | DIV  -> 21 
  | MUL  -> 22 
  | NOT  -> 23 
  | MINUS  -> 24 
  | EQ  -> 25 
  | LTN  -> 26 
  | GTN  -> 27 
  | NEQ  -> 28 
  | LEQ  -> 29 
  | GEQ  -> 30 
  | DO  -> 31 
  | IF  -> 32 
  | ASGN  -> 33 
  | COLON  -> 34 
  | NUMBER _ -> 35 
  | ID _ -> 36 

// This function maps integers indexes to symbolic token ids
let tokenTagToTokenId (tokenIdx:int) = 
  match tokenIdx with
  | 0 -> TOKEN_EOF 
  | 1 -> TOKEN_ABORT 
  | 2 -> TOKEN_READ 
  | 3 -> TOKEN_WRITE 
  | 4 -> TOKEN_TRUE 
  | 5 -> TOKEN_FALSE 
  | 6 -> TOKEN_OD 
  | 7 -> TOKEN_FI 
  | 8 -> TOKEN_LPAREN 
  | 9 -> TOKEN_RPAREN 
  | 10 -> TOKEN_LBRACK 
  | 11 -> TOKEN_RBRACK 
  | 12 -> TOKEN_GUARD 
  | 13 -> TOKEN_MODULE 
  | 14 -> TOKEN_END 
  | 15 -> TOKEN_SEMICOLON 
  | 16 -> TOKEN_ARROW 
  | 17 -> TOKEN_SKIP 
  | 18 -> TOKEN_OR 
  | 19 -> TOKEN_AND 
  | 20 -> TOKEN_ADD 
  | 21 -> TOKEN_DIV 
  | 22 -> TOKEN_MUL 
  | 23 -> TOKEN_NOT 
  | 24 -> TOKEN_MINUS 
  | 25 -> TOKEN_EQ 
  | 26 -> TOKEN_LTN 
  | 27 -> TOKEN_GTN 
  | 28 -> TOKEN_NEQ 
  | 29 -> TOKEN_LEQ 
  | 30 -> TOKEN_GEQ 
  | 31 -> TOKEN_DO 
  | 32 -> TOKEN_IF 
  | 33 -> TOKEN_ASGN 
  | 34 -> TOKEN_COLON 
  | 35 -> TOKEN_NUMBER 
  | 36 -> TOKEN_ID 
  | 39 -> TOKEN_end_of_input
  | 37 -> TOKEN_error
  | _ -> failwith "tokenTagToTokenId: bad token"

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
let prodIdxToNonTerminal (prodIdx:int) = 
  match prodIdx with
    | 0 -> NONTERM__startstart 
    | 1 -> NONTERM_start 
    | 2 -> NONTERM_LangProgram 
    | 3 -> NONTERM_Command 
    | 4 -> NONTERM_Command 
    | 5 -> NONTERM_Command 
    | 6 -> NONTERM_Command 
    | 7 -> NONTERM_Command 
    | 8 -> NONTERM_Command 
    | 9 -> NONTERM_Command 
    | 10 -> NONTERM_Command 
    | 11 -> NONTERM_Command 
    | 12 -> NONTERM_GCmd 
    | 13 -> NONTERM_GCmd 
    | 14 -> NONTERM_Arrow 
    | 15 -> NONTERM_Expression 
    | 16 -> NONTERM_Expression 
    | 17 -> NONTERM_Expression 
    | 18 -> NONTERM_Expression 
    | 19 -> NONTERM_Expression 
    | 20 -> NONTERM_Expression 
    | 21 -> NONTERM_Expression 
    | 22 -> NONTERM_Expression 
    | 23 -> NONTERM_Expression 
    | 24 -> NONTERM_Expression 
    | 25 -> NONTERM_Expression 
    | 26 -> NONTERM_Expression 
    | 27 -> NONTERM_Expression 
    | 28 -> NONTERM_Expression 
    | 29 -> NONTERM_Expression 
    | 30 -> NONTERM_Expression 
    | 31 -> NONTERM_Expression 
    | 32 -> NONTERM_Expression 
    | 33 -> NONTERM_Expression 
    | _ -> failwith "prodIdxToNonTerminal: bad production index"

let _fsyacc_endOfInputTag = 39 
let _fsyacc_tagOfErrorTerminal = 37

// This function gets the name of a token as a string
let token_to_string (t:token) = 
  match t with 
  | EOF  -> "EOF" 
  | ABORT  -> "ABORT" 
  | READ  -> "READ" 
  | WRITE  -> "WRITE" 
  | TRUE  -> "TRUE" 
  | FALSE  -> "FALSE" 
  | OD  -> "OD" 
  | FI  -> "FI" 
  | LPAREN  -> "LPAREN" 
  | RPAREN  -> "RPAREN" 
  | LBRACK  -> "LBRACK" 
  | RBRACK  -> "RBRACK" 
  | GUARD  -> "GUARD" 
  | MODULE  -> "MODULE" 
  | END  -> "END" 
  | SEMICOLON  -> "SEMICOLON" 
  | ARROW  -> "ARROW" 
  | SKIP  -> "SKIP" 
  | OR  -> "OR" 
  | AND  -> "AND" 
  | ADD  -> "ADD" 
  | DIV  -> "DIV" 
  | MUL  -> "MUL" 
  | NOT  -> "NOT" 
  | MINUS  -> "MINUS" 
  | EQ  -> "EQ" 
  | LTN  -> "LTN" 
  | GTN  -> "GTN" 
  | NEQ  -> "NEQ" 
  | LEQ  -> "LEQ" 
  | GEQ  -> "GEQ" 
  | DO  -> "DO" 
  | IF  -> "IF" 
  | ASGN  -> "ASGN" 
  | COLON  -> "COLON" 
  | NUMBER _ -> "NUMBER" 
  | ID _ -> "ID" 

// This function gets the data carried by a token as an object
let _fsyacc_dataOfToken (t:token) = 
  match t with 
  | EOF  -> (null : System.Object) 
  | ABORT  -> (null : System.Object) 
  | READ  -> (null : System.Object) 
  | WRITE  -> (null : System.Object) 
  | TRUE  -> (null : System.Object) 
  | FALSE  -> (null : System.Object) 
  | OD  -> (null : System.Object) 
  | FI  -> (null : System.Object) 
  | LPAREN  -> (null : System.Object) 
  | RPAREN  -> (null : System.Object) 
  | LBRACK  -> (null : System.Object) 
  | RBRACK  -> (null : System.Object) 
  | GUARD  -> (null : System.Object) 
  | MODULE  -> (null : System.Object) 
  | END  -> (null : System.Object) 
  | SEMICOLON  -> (null : System.Object) 
  | ARROW  -> (null : System.Object) 
  | SKIP  -> (null : System.Object) 
  | OR  -> (null : System.Object) 
  | AND  -> (null : System.Object) 
  | ADD  -> (null : System.Object) 
  | DIV  -> (null : System.Object) 
  | MUL  -> (null : System.Object) 
  | NOT  -> (null : System.Object) 
  | MINUS  -> (null : System.Object) 
  | EQ  -> (null : System.Object) 
  | LTN  -> (null : System.Object) 
  | GTN  -> (null : System.Object) 
  | NEQ  -> (null : System.Object) 
  | LEQ  -> (null : System.Object) 
  | GEQ  -> (null : System.Object) 
  | DO  -> (null : System.Object) 
  | IF  -> (null : System.Object) 
  | ASGN  -> (null : System.Object) 
  | COLON  -> (null : System.Object) 
  | NUMBER _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
  | ID _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
let _fsyacc_gotos = [| 0us; 65535us; 1us; 65535us; 0us; 1us; 1us; 65535us; 0us; 2us; 4us; 65535us; 5us; 6us; 20us; 17us; 21us; 18us; 30us; 19us; 3us; 65535us; 23us; 24us; 26us; 27us; 32us; 31us; 1us; 65535us; 29us; 30us; 20us; 65535us; 9us; 10us; 15us; 16us; 23us; 29us; 26us; 29us; 32us; 29us; 38us; 39us; 55us; 41us; 56us; 42us; 57us; 43us; 58us; 44us; 59us; 45us; 60us; 46us; 61us; 47us; 62us; 48us; 63us; 49us; 64us; 50us; 65us; 51us; 66us; 52us; 67us; 53us; 68us; 54us; |]
let _fsyacc_sparseGotoTableRowOffsets = [|0us; 1us; 3us; 5us; 10us; 14us; 16us; |]
let _fsyacc_stateToProdIdxsTableElements = [| 1us; 0us; 1us; 0us; 1us; 1us; 1us; 2us; 1us; 2us; 1us; 2us; 2us; 2us; 8us; 1us; 2us; 1us; 3us; 1us; 3us; 13us; 3us; 20us; 21us; 22us; 23us; 24us; 25us; 28us; 29us; 30us; 31us; 32us; 33us; 1us; 4us; 1us; 5us; 1us; 6us; 1us; 6us; 1us; 7us; 13us; 7us; 20us; 21us; 22us; 23us; 24us; 25us; 28us; 29us; 30us; 31us; 32us; 33us; 2us; 8us; 8us; 2us; 8us; 9us; 2us; 8us; 12us; 1us; 8us; 1us; 9us; 1us; 9us; 1us; 10us; 2us; 10us; 13us; 1us; 10us; 1us; 11us; 2us; 11us; 13us; 1us; 11us; 13us; 12us; 20us; 21us; 22us; 23us; 24us; 25us; 28us; 29us; 30us; 31us; 32us; 33us; 1us; 12us; 2us; 13us; 13us; 1us; 13us; 1us; 14us; 1us; 15us; 1us; 16us; 1us; 17us; 1us; 18us; 1us; 19us; 13us; 19us; 20us; 21us; 22us; 23us; 24us; 25us; 28us; 29us; 30us; 31us; 32us; 33us; 1us; 19us; 13us; 20us; 20us; 21us; 22us; 23us; 24us; 25us; 28us; 29us; 30us; 31us; 32us; 33us; 13us; 20us; 21us; 21us; 22us; 23us; 24us; 25us; 28us; 29us; 30us; 31us; 32us; 33us; 13us; 20us; 21us; 22us; 22us; 23us; 24us; 25us; 28us; 29us; 30us; 31us; 32us; 33us; 13us; 20us; 21us; 22us; 23us; 23us; 24us; 25us; 28us; 29us; 30us; 31us; 32us; 33us; 13us; 20us; 21us; 22us; 23us; 24us; 24us; 25us; 28us; 29us; 30us; 31us; 32us; 33us; 13us; 20us; 21us; 22us; 23us; 24us; 25us; 25us; 28us; 29us; 30us; 31us; 32us; 33us; 13us; 20us; 21us; 22us; 23us; 24us; 25us; 26us; 28us; 29us; 30us; 31us; 32us; 33us; 13us; 20us; 21us; 22us; 23us; 24us; 25us; 27us; 28us; 29us; 30us; 31us; 32us; 33us; 13us; 20us; 21us; 22us; 23us; 24us; 25us; 28us; 28us; 29us; 30us; 31us; 32us; 33us; 13us; 20us; 21us; 22us; 23us; 24us; 25us; 28us; 29us; 29us; 30us; 31us; 32us; 33us; 13us; 20us; 21us; 22us; 23us; 24us; 25us; 28us; 29us; 30us; 30us; 31us; 32us; 33us; 13us; 20us; 21us; 22us; 23us; 24us; 25us; 28us; 29us; 30us; 31us; 31us; 32us; 33us; 13us; 20us; 21us; 22us; 23us; 24us; 25us; 28us; 29us; 30us; 31us; 32us; 32us; 33us; 13us; 20us; 21us; 22us; 23us; 24us; 25us; 28us; 29us; 30us; 31us; 32us; 33us; 33us; 1us; 20us; 1us; 21us; 1us; 22us; 1us; 23us; 1us; 24us; 1us; 25us; 1us; 26us; 1us; 27us; 1us; 28us; 1us; 29us; 1us; 30us; 1us; 31us; 1us; 32us; 1us; 33us; |]
let _fsyacc_stateToProdIdxsTableRowOffsets = [|0us; 2us; 4us; 6us; 8us; 10us; 12us; 15us; 17us; 19us; 21us; 35us; 37us; 39us; 41us; 43us; 45us; 59us; 62us; 65us; 68us; 70us; 72us; 74us; 76us; 79us; 81us; 83us; 86us; 88us; 102us; 104us; 107us; 109us; 111us; 113us; 115us; 117us; 119us; 121us; 135us; 137us; 151us; 165us; 179us; 193us; 207us; 221us; 235us; 249us; 263us; 277us; 291us; 305us; 319us; 333us; 335us; 337us; 339us; 341us; 343us; 345us; 347us; 349us; 351us; 353us; 355us; 357us; 359us; |]
let _fsyacc_action_rows = 69
let _fsyacc_actionTableElements = [|1us; 32768us; 13us; 3us; 0us; 49152us; 0us; 16385us; 1us; 32768us; 36us; 4us; 1us; 32768us; 34us; 5us; 8us; 32768us; 1us; 12us; 2us; 13us; 3us; 15us; 10us; 21us; 17us; 11us; 31us; 23us; 32us; 26us; 36us; 8us; 2us; 32768us; 14us; 7us; 15us; 20us; 0us; 16386us; 1us; 32768us; 33us; 9us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 12us; 16387us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 0us; 16388us; 0us; 16389us; 1us; 32768us; 36us; 14us; 0us; 16390us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 12us; 16391us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 1us; 16392us; 15us; 20us; 2us; 32768us; 11us; 22us; 15us; 20us; 1us; 16396us; 15us; 20us; 8us; 32768us; 1us; 12us; 2us; 13us; 3us; 15us; 10us; 21us; 17us; 11us; 31us; 23us; 32us; 26us; 36us; 8us; 8us; 32768us; 1us; 12us; 2us; 13us; 3us; 15us; 10us; 21us; 17us; 11us; 31us; 23us; 32us; 26us; 36us; 8us; 0us; 16393us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 2us; 32768us; 6us; 25us; 12us; 32us; 0us; 16394us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 2us; 32768us; 7us; 28us; 12us; 32us; 0us; 16395us; 13us; 32768us; 16us; 33us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 8us; 32768us; 1us; 12us; 2us; 13us; 3us; 15us; 10us; 21us; 17us; 11us; 31us; 23us; 32us; 26us; 36us; 8us; 1us; 16397us; 12us; 32us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 0us; 16398us; 0us; 16399us; 0us; 16400us; 0us; 16401us; 0us; 16402us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 13us; 32768us; 9us; 40us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 0us; 16403us; 12us; 16404us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16405us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16406us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16407us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16408us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16409us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16410us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16411us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16412us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16413us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16414us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16415us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16416us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 12us; 16417us; 18us; 59us; 19us; 60us; 20us; 55us; 21us; 58us; 22us; 57us; 24us; 56us; 25us; 67us; 26us; 64us; 27us; 63us; 28us; 68us; 29us; 66us; 30us; 65us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; 7us; 32768us; 4us; 36us; 5us; 37us; 8us; 38us; 23us; 61us; 24us; 62us; 35us; 35us; 36us; 34us; |]
let _fsyacc_actionTableRowOffsets = [|0us; 2us; 3us; 4us; 6us; 8us; 17us; 20us; 21us; 23us; 31us; 44us; 45us; 46us; 48us; 49us; 57us; 70us; 72us; 75us; 77us; 86us; 95us; 96us; 104us; 107us; 108us; 116us; 119us; 120us; 134us; 143us; 145us; 153us; 154us; 155us; 156us; 157us; 158us; 166us; 180us; 181us; 194us; 207us; 220us; 233us; 246us; 259us; 272us; 285us; 298us; 311us; 324us; 337us; 350us; 363us; 371us; 379us; 387us; 395us; 403us; 411us; 419us; 427us; 435us; 443us; 451us; 459us; 467us; |]
let _fsyacc_reductionSymbolCounts = [|1us; 1us; 5us; 3us; 1us; 1us; 2us; 2us; 3us; 3us; 3us; 3us; 3us; 3us; 1us; 1us; 1us; 1us; 1us; 3us; 3us; 3us; 3us; 3us; 3us; 3us; 2us; 2us; 3us; 3us; 3us; 3us; 3us; 3us; |]
let _fsyacc_productionToNonTerminalTable = [|0us; 1us; 2us; 3us; 3us; 3us; 3us; 3us; 3us; 3us; 3us; 3us; 4us; 4us; 5us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; 6us; |]
let _fsyacc_immediateActions = [|65535us; 49152us; 16385us; 65535us; 65535us; 65535us; 65535us; 16386us; 65535us; 65535us; 65535us; 16388us; 16389us; 65535us; 16390us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 16393us; 65535us; 65535us; 16394us; 65535us; 65535us; 16395us; 65535us; 65535us; 65535us; 65535us; 16398us; 16399us; 16400us; 16401us; 16402us; 65535us; 65535us; 16403us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; |]
let _fsyacc_reductions ()  =    [| 
# 329 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : Program)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
                      raise (Microsoft.FSharp.Text.Parsing.Accept(Microsoft.FSharp.Core.Operators.box _1))
                   )
                 : '_startstart));
# 338 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'LangProgram)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 30 "LangParser.fsp"
                                          _1 
                   )
# 30 "LangParser.fsp"
                 : Program));
# 349 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : string)) in
            let _4 = (let data = parseState.GetInput(4) in (Microsoft.FSharp.Core.Operators.unbox data : Cmd)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 32 "LangParser.fsp"
                                                                Program(_2, _4) 
                   )
# 32 "LangParser.fsp"
                 : 'LangProgram));
# 361 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : string)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 35 "LangParser.fsp"
                                            Asgn(_1, _3, labelCmd())
                   )
# 35 "LangParser.fsp"
                 : Cmd));
# 373 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 36 "LangParser.fsp"
                               Skip(labelCmd()) 
                   )
# 36 "LangParser.fsp"
                 : Cmd));
# 383 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 37 "LangParser.fsp"
                                Abort(labelCmd()) 
                   )
# 37 "LangParser.fsp"
                 : Cmd));
# 393 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : string)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 38 "LangParser.fsp"
                                  Read(_2, labelCmd()) 
                   )
# 38 "LangParser.fsp"
                 : Cmd));
# 404 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 39 "LangParser.fsp"
                                           Write(_2, labelCmd()) 
                   )
# 39 "LangParser.fsp"
                 : Cmd));
# 415 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : Cmd)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : Cmd)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 40 "LangParser.fsp"
                                                    Seq(_1, _3) 
                   )
# 40 "LangParser.fsp"
                 : Cmd));
# 427 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : Cmd)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 41 "LangParser.fsp"
                                                _2 
                   )
# 41 "LangParser.fsp"
                 : Cmd));
# 438 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : 'GCmd)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 42 "LangParser.fsp"
                                     Do(_2) 
                   )
# 42 "LangParser.fsp"
                 : Cmd));
# 449 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : 'GCmd)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 43 "LangParser.fsp"
                                     If(_2) 
                   )
# 43 "LangParser.fsp"
                 : Cmd));
# 460 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : 'Arrow)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : Cmd)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 46 "LangParser.fsp"
                                                   SingleGuard(_1,_2,_3) 
                   )
# 46 "LangParser.fsp"
                 : 'GCmd));
# 473 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'GCmd)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'GCmd)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 47 "LangParser.fsp"
                                          ComplexGuard(_1,_3) 
                   )
# 47 "LangParser.fsp"
                 : 'GCmd));
# 485 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 50 "LangParser.fsp"
                               labelCmd(); GuardLabel(getLabel())
                   )
# 50 "LangParser.fsp"
                 : 'Arrow));
# 495 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : string)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 53 "LangParser.fsp"
                                Var(_1) 
                   )
# 53 "LangParser.fsp"
                 : 'Expression));
# 506 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : int)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 54 "LangParser.fsp"
                                    Int(_1) 
                   )
# 54 "LangParser.fsp"
                 : 'Expression));
# 517 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 55 "LangParser.fsp"
                               True 
                   )
# 55 "LangParser.fsp"
                 : 'Expression));
# 527 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 56 "LangParser.fsp"
                                False 
                   )
# 56 "LangParser.fsp"
                 : 'Expression));
# 537 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 57 "LangParser.fsp"
                                                   _2 
                   )
# 57 "LangParser.fsp"
                 : 'Expression));
# 548 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 58 "LangParser.fsp"
                                                       Add(_1, _3) 
                   )
# 58 "LangParser.fsp"
                 : 'Expression));
# 560 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 59 "LangParser.fsp"
                                                         Sub(_1, _3) 
                   )
# 59 "LangParser.fsp"
                 : 'Expression));
# 572 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 60 "LangParser.fsp"
                                                       Mul(_1, _3) 
                   )
# 60 "LangParser.fsp"
                 : 'Expression));
# 584 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 61 "LangParser.fsp"
                                                       Div(_1, _3) 
                   )
# 61 "LangParser.fsp"
                 : 'Expression));
# 596 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 62 "LangParser.fsp"
                                                      Or(_1, _3) 
                   )
# 62 "LangParser.fsp"
                 : 'Expression));
# 608 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 63 "LangParser.fsp"
                                                       And(_1, _3) 
                   )
# 63 "LangParser.fsp"
                 : 'Expression));
# 620 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 64 "LangParser.fsp"
                                            Not(_2) 
                   )
# 64 "LangParser.fsp"
                 : 'Expression));
# 631 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 65 "LangParser.fsp"
                                           Minus(_2) 
                   )
# 65 "LangParser.fsp"
                 : 'Expression));
# 642 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 66 "LangParser.fsp"
                                                       Gtn(_1, _3) 
                   )
# 66 "LangParser.fsp"
                 : 'Expression));
# 654 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 67 "LangParser.fsp"
                                                       Ltn(_1, _3) 
                   )
# 67 "LangParser.fsp"
                 : 'Expression));
# 666 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 68 "LangParser.fsp"
                                                    Geq(_1, _3) 
                   )
# 68 "LangParser.fsp"
                 : 'Expression));
# 678 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 69 "LangParser.fsp"
                                                       Leq(_1, _3) 
                   )
# 69 "LangParser.fsp"
                 : 'Expression));
# 690 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 70 "LangParser.fsp"
                                                   Eq(_1, _3) 
                   )
# 70 "LangParser.fsp"
                 : 'Expression));
# 702 "LangParser.fs"
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : 'Expression)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 71 "LangParser.fsp"
                                                       Neq(_1, _3) 
                   )
# 71 "LangParser.fsp"
                 : 'Expression));
|]
# 715 "LangParser.fs"
let tables () : Microsoft.FSharp.Text.Parsing.Tables<_> = 
  { reductions= _fsyacc_reductions ();
    endOfInputTag = _fsyacc_endOfInputTag;
    tagOfToken = tagOfToken;
    dataOfToken = _fsyacc_dataOfToken; 
    actionTableElements = _fsyacc_actionTableElements;
    actionTableRowOffsets = _fsyacc_actionTableRowOffsets;
    stateToProdIdxsTableElements = _fsyacc_stateToProdIdxsTableElements;
    stateToProdIdxsTableRowOffsets = _fsyacc_stateToProdIdxsTableRowOffsets;
    reductionSymbolCounts = _fsyacc_reductionSymbolCounts;
    immediateActions = _fsyacc_immediateActions;
    gotos = _fsyacc_gotos;
    sparseGotoTableRowOffsets = _fsyacc_sparseGotoTableRowOffsets;
    tagOfErrorTerminal = _fsyacc_tagOfErrorTerminal;
    parseError = (fun (ctxt:Microsoft.FSharp.Text.Parsing.ParseErrorContext<_>) -> 
                              match parse_error_rich with 
                              | Some f -> f ctxt
                              | None -> parse_error ctxt.Message);
    numTerminals = 40;
    productionToNonTerminalTable = _fsyacc_productionToNonTerminalTable  }
let engine lexer lexbuf startState = (tables ()).Interpret(lexer, lexbuf, startState)
let start lexer lexbuf : Program =
    Microsoft.FSharp.Core.Operators.unbox ((tables ()).Interpret(lexer, lexbuf, 0))
