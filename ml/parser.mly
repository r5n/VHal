%{
    open Vhal
%}

%token <string> IDENT
%token LPAREN
%token RPAREN
%token PERIOD
%token ALL EX
%token IMPL IFF
%token AND OR
%token NEG
%token COMMA
%token QUESTION
%token EOF

%left IMPL IFF
%left OR
%left AND
%nonassoc NEG

%start <Vhal.formula> main
%%

main: form EOF                            { $1 }

form:
  | LPAREN; ALL; x = IDENT; PERIOD; f = form; RPAREN { makeForall x f }
  | LPAREN; EX; x = IDENT; PERIOD; f = form; RPAREN  { makeExists x f }
  | f1 = form; AND; f2 = form                        { makeConn "&" f1 f2 }
  | f1 = form; OR; f2 = form                         { makeConn "|" f1 f2 }
  | f1 = form; IMPL; f2 = form                       { makeConn "-->" f1 f2 }
  | f1 = form; IFF; f2 = form                        { makeConn "<->" f1 f2 }
  | NEG; f = form                                    { makeNeg f }
  | x = IDENT                                        { Pred(stocs x, []) }
  | x = IDENT; LPAREN; ts = terms; RPAREN            { Pred(stocs x, ts) }
  | LPAREN; f = form; RPAREN                         { f }
  ;


terms: ts = LPAREN; separated_list(COMMA, term); RPAREN { ts };

term:
  | x = IDENT; ys = terms { Fun(stocs x, ys) }
  | QUESTION; x = IDENT   { Var(stocs x) }
  ;
