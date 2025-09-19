%token LBRACK RBRACK LPAREN RPAREN
%token LETC LETP
%token <string> IDENT
%token <string> COIDENT
%token EOF
%start <Ast.Surface.t> prog
%%

prog: 
  | c=cut EOF { c }

cut: 
  | LBRACK p=producer c=consumer RBRACK { {p; c} }

producer:
  | v = IDENT { Ast.Surface.V v }
  | LPAREN LETC cv=COIDENT c=cut RPAREN { Ast.Surface.Mu (cv, c) }

consumer: 
  | cv = COIDENT { Ast.Surface.C cv }
  | LPAREN LETP v=IDENT c=cut RPAREN { Ast.Surface.MuTilde (v, c) }
