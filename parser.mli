type token =
    | BOOL of (bool)
    | INT of (int)
    | FLOAT of (float)
    | NOT
    | MINUS
    | PLUS
    | EQUAL
    | IF
    | THEN
    | ELSE
    | LET
    | REC
    | SEMICOLON
    | DOT
    | COMMA
    | LPAREN
    | RPAREN
    | EOF

val exp : 
(Lexing.lexbuf -> token) -> Lexing.lexbuf -> Syntax.t