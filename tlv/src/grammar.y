%{
#include <storage.h>
#include <node.h>
#include <node_smv.h>
#include <script.h>

#include <tlv.h>
#include <util_err.h>

char do_prompt = 0;


node_ptr parse_tree;
node_ptr iparse_tree = NIL;

extern set_prompt();


%}

%union {
  node_ptr node;
}

/* all of the terminal grammar symbols (tokens recognized
by the lexical analyzer)
note: all binary operators associate from left to right
ops are listed from lowest to highest priority */

%left TLV_RETURN CONTINUE BREAK SETTIME CHKTIME
/* LOAD */
%left LET LOCAL EXIST TNO SIZE DUMP QUANT PRINT GOTO TO RUN END WHILE TLVFOR FIX TLVCASE IF ELSE PROC CALL FUNC
%left EXIT INOUT
%left CTL LTL
%left ASYNC MODULE PROCESS SYSTEM MODTYPE LAMBDA CONTEXT EU AU EBU ABU
%left VAR DEFINE INIT TRANS INVAR FORMAT SPEC FAIRNESS ISA CONSTANT ASSIGN JUSTICE COMPASSION STRUCTURE OWNED
%left INPUT OUTPUT IMPLEMENTS
%left BOOLEAN ARRAY OF KIND SCALAR LIST OVER BDD FOR IFSMV ELSESMV
%left SEMI QUOTE_LP LP RP LB RB LCB RCB
%left EQDEF TWODOTS ATLINE THREEDOTS
%left <node> FALSEEXP TRUEEXP
%left APROPOS SELF SIGMA
%right QUESTION COLON 
%left CASE ESAC 
%left REVERSE

%left <node> ATOM
%left <node> NUMBER
%left <node> QUOTE

%left DEFAULT
%left  COMMA
%left  QUOTECHAR
%left  IMPLIES
%left  IFF
%left  OR FORSOME
%left  AND FASTAND FORALL
%left  NOT
%left  EX AX EF AF EG AG E A UNTIL EBF EBG ABF ABG BUNTIL
%left  ENTAILS CONGRUENT
%right LTLUNTIL WAITINGFOR SINCE BACKTO
%left  NEXT_LTL EVENTUALLY ALWAYS HASALWAYSBEEN ONCE PREVIOUSLY WEAKPREVIOUS
%left  EQUAL NOTEQUAL LT GT LE GE STRING_EQ
%left  UNION
%left  SETIN SETNOTIN
%left  MOD
%left  PLUS MINUS ASYNCHCOMP
%left  TIMES DIVIDE SYNCHCOMP
%left  UMINUS		/* supplies precedence for unary minus */
%left  NEXT SMALLINIT SAT
%left  DOT



/* all nonterminals return a parse tree node */
%type <node> modules module declarations declaration var vlist vitem justice compassion
%type <node> commandlist basicstmt
%type <node> type isa init trans invar define dlist ditem spec fairness cexpr functioncall
%type <node> owned structure structexpr for_clause
%type <node> neatomlist term nterm qualifiedterm subrange neparamlist paramlist
%type <node> number expr nexpr atomic_form ctl_formula ltl_formula caselist constant qualifiedatom
%type <node> tlvcaselist  quotelist setconst kind_classification
%type <node> moduletype usertype expritem neexprlist neqexprlist assign alist aitem alhs neatomset
%type <node> input output implements netermlist neconstlist exprlist comppair necomppair
/*atomlist*/
%type <node> istmt stmt stmts


%start begin
%%
begin         : modules {parse_tree = $1;}
              | commandlist { iparse_tree = $1 ; YYACCEPT;}
              ;

modules       : module {$$ = cons($1,NIL);}
              | modules module {$$ = cons($2,$1);}
              ;


module        : MODULE moduletype declarations {$$ = new_module($2,$3);}
              ;

moduletype    : ATOM {$$ = new_signature($1,NIL);}
              | ATOM LP neatomlist RP {$$ = new_signature($1,$3);}
              ;

declarations  : {$$ = NIL;}
              | declarations declaration {$$ = cons($2,$1);}
              ;

declaration   : var
              | isa
              | init
              | trans
              | invar
              | define
              | spec
              | fairness
              | assign 
              | input
              | output
              | implements
              | justice
              | compassion
              | structure
              | owned
              ;

implements    : IMPLEMENTS ATOM {$$ = new_node(IMPLEMENTS,$2,NIL);}
              ;

justice       : JUSTICE neexprlist {$$ = new_node(JUSTICE,$2,NIL);}
              ;

owned         : OWNED netermlist {$$ = new_node(OWNED,$2,NIL);}
              ;

structexpr    : term { $$ = $1;}
              | LP structexpr RP { $$ = $2;}
              | structexpr ASYNCHCOMP structexpr { $$ = new_node(ASYNCHCOMP,$1,$3);}
              | structexpr SYNCHCOMP structexpr { $$ = new_node(SYNCHCOMP,$1,$3);}
              | ASYNCHCOMP for_clause LCB structexpr RCB
                  { $2->type = ASYNCHCOMP; $$ = new_node(FOR,$2,$4); }
              | SYNCHCOMP for_clause LCB structexpr RCB
                  { $2->type = SYNCHCOMP; $$ = new_node(FOR,$2,$4); }
              ;

structure     : STRUCTURE structexpr { $$ = new_node(STRUCTURE,$2,NIL);}
              ;

comppair      : LP expr COMMA expr RP {$$ = cons($2,$4);}
              | for_clause LCB necomppair RCB  {$$ = new_node(FOR,$1,$3);}
              | IFSMV LP expr RP LCB necomppair RCB
                {$$ = new_smv_if($3,$6,NIL);}
              | IFSMV LP expr RP LCB necomppair RCB ELSESMV LCB necomppair RCB
                {$$ = new_smv_if($3,$6,$10);}
              ;

necomppair    : comppair {$$ = cons($1,NIL);}
              | necomppair COMMA comppair {$$ = cons($3,$1);}
              ;

compassion    : COMPASSION necomppair {$$ = new_node(COMPASSION,$2,NIL);}
              ;

var           : VAR vlist {$$ = new_node(VAR,$2,NIL);}
              ;

input         : INPUT vlist {$$ = new_node(INPUT,$2,NIL);}
              ;

output        : OUTPUT netermlist SEMI {$$ = new_node(OUTPUT,$2,NIL);}
              ;

vitem         : term COLON type SEMI            {$$ = new_node(COLON,$1,$3); }
              | for_clause LCB vlist RCB        {$$ = new_node(FOR,$1,$3);   }
              | IFSMV LP expr RP LCB vlist RCB  {$$ = new_smv_if($3,$6,NIL); }
              | IFSMV LP expr RP LCB vlist RCB ELSESMV LCB vlist RCB
                {$$ = new_smv_if($3,$6,$10);}
              ;

vlist         : {$$ = NIL;}
              | vlist vitem  {$$ = cons($2,$1);}
              ;

kind_classification : { $$ = NIL; }
              | KIND OF neatomlist { $$ = $3; }
              ;

type          : BOOLEAN kind_classification {$$ = new_node(BOOLEAN,NIL,$2);}
              | LCB neconstlist RCB kind_classification {$$ = new_node(SCALAR,$2,$4);}
              | subrange kind_classification { $$ = new_node(TWODOTS,$1,$2); }
              | usertype
              | ARRAY subrange OF type {$$ = new_node(ARRAY,$2,$4);}
              | PROCESS usertype {$$ = new_node(PROCESS,$2,NIL);}
              | SYSTEM usertype {$$ = new_node(SYSTEM,$2,NIL);}
              ;

usertype      : ATOM {$$ = new_node(MODTYPE,$1,NIL);}
              | ATOM LP neexprlist RP {$$ = new_node(MODTYPE,$1,$3);}
              ;

/* subrange      : number TWODOTS expr {$$ = new_node(TWODOTS,$1,$3);} */
subrange      : number TWODOTS cexpr {$$ = new_node(TWODOTS,$1,$3);}
              ;

isa           : ISA ATOM {$$ = new_node(ISA,$2,NIL);}
              ;

init          : INIT expr {$$ = new_node(INIT,$2,NIL);}
              ;

trans         : TRANS expr {$$ = new_node(TRANS,$2,NIL);}
              ;

invar         : INVAR expr {$$ = new_node(INVAR,$2,NIL);}
              ;

define        : DEFINE dlist {$$ = new_node(DEFINE,$2,NIL);}
              ;

ditem         : term COLON LTL LP ltl_formula RP SEMI{$$ = new_node(LTL,$1,$5);}
              | term EQDEF expr SEMI {$$ = new_node(EQDEF,$1,$3);}
              | for_clause LCB dlist RCB  
                {$$ = new_node(FOR,$1,$3);}
              | IFSMV LP expr RP LCB dlist RCB
                {$$ = new_smv_if($3,$6,NIL);}
              | IFSMV LP expr RP LCB dlist RCB ELSESMV LCB dlist RCB
                {$$ = new_smv_if($3,$6,$10);}
              ;

dlist         : {$$ = NIL;}
              | dlist ditem {$$ = cons($2,$1);}
              ;

assign        : ASSIGN alist {$$ = new_node(ASSIGN,$2,NIL);}
              ;
 
alist         : {$$ = NIL;}
              | alist aitem {$$ = new_node(AND,$2,$1);}
              ;

aitem         : alhs EQDEF expr SEMI { $$ = new_smv_assignment($1, $3);}
              | for_clause LCB alist RCB { $$ = new_node(FOR,$1,$3);}
              | DEFAULT LCB alist RCB SETIN LCB alist RCB { $$ = new_node(DEFAULT,$3,$7);}
              ; 

alhs          : term                 {$$ = new_left_hand_side(CURRENT_ASS,$1);}
              | NEXT LP term RP      {$$ = new_left_hand_side(NEXT,$3);}
              | SMALLINIT LP term RP {$$ = new_left_hand_side(SMALLINIT,$3);}
              ;

spec          : SPEC ctl_formula {$$ = new_node(SPEC,$2,NIL);}
              ;

fairness      : FAIRNESS ctl_formula {$$ = new_node(FAIRNESS,$2,NIL);}
              ;


neconstlist   : constant {$$ = cons(find_atom($1),NIL);}
              | neconstlist COMMA constant {$$ = cons(find_atom($3),$1);}
              ;

neatomlist    : ATOM {$$ = cons(find_atom($1),NIL);}
              | neatomlist COMMA ATOM {$$ = cons(find_atom($3),$1);}
              ;

/*atomlist      : {$$ = NIL;}
              | neatomlist */

expritem      : expr {$$ = $1;}
              | for_clause LCB neexprlist RCB  {$$ = cons(new_node(FOR,$1,$3),NIL);}
              | IFSMV LP expr RP LCB neexprlist RCB
                  {$$ = new_smv_if($3,$6,NIL);}     
              | IFSMV LP expr RP LCB neexprlist RCB ELSESMV LCB neexprlist RCB
                  {$$ = new_smv_if($3,$6,$10);}
              ;

neexprlist    : expritem {$$ = cons($1,NIL);}
              | neexprlist COMMA expritem {$$ = cons($3,$1);}
              ;

/* neqexprlist == Qualified neexprelist */
neqexprlist   : expr {$$ = cons($1,NIL);}
              | QUOTECHAR expr {$$ = cons(find_node(DEFINE,$2,NIL),NIL);}
              | neqexprlist COMMA expr {$$ = cons($3,$1);}
              | neqexprlist COMMA QUOTECHAR expr {$$ = cons(find_node(DEFINE,$4,NIL),$1);}
              ;

exprlist      : {$$ = NIL;}
              | neexprlist 
              ;

netermlist    : term {$$ = cons($1,NIL);} 
              | netermlist COMMA term {$$ = cons($3,$1);}
              | for_clause LCB netermlist RCB  {$$ = cons(new_node(FOR,$1,$3),NIL);}
              | netermlist COMMA for_clause LCB netermlist RCB 
                {$$ = cons(new_node(FOR,$3,$5),$1);}
              ;

term          : ATOM
              | SELF {$$ = new_node(SELF,NIL,NIL);}
              | term DOT ATOM {$$ = new_node(DOT,$1,$3);}
              | term LB expr RB {$$ = new_node(ARRAY,$1,$3);}
              ;

number        : NUMBER
	      | PLUS NUMBER %prec UMINUS
		{ $$ = $2; }
	      | MINUS NUMBER %prec UMINUS
		{$2->left.inttype = -($2->left.inttype); $$ = $2;}
              ;

/* cexpr - constant expression, i.e. an expression which should 
   evaluate to an integer constant. */
cexpr         : term
              | number
	      | LP cexpr RP { $$ = $2; }
              | cexpr PLUS cexpr { $$ = new_node(PLUS,$1,$3); }
              | cexpr MINUS cexpr { $$ = new_node(MINUS,$1,$3); }
              | cexpr TIMES cexpr { $$ = new_node(TIMES,$1,$3); }
              | cexpr DIVIDE cexpr { $$ = new_node(DIVIDE,$1,$3); }
              | cexpr MOD cexpr { $$ = new_node(MOD,$1,$3); }
              ;

for_clause    : FOR LP ATOM EQUAL expr SEMI expr SEMI ATOM EQUAL expr RP 
                {$$ = cons(cons($3,$5),cons($7,$11))}
              ;

setconst      : LCB neatomset RCB { $$ = $2; } 
              ;

nterm         : term { $$ = $1; }
              | NEXT LP term RP { $$ = new_node(NEXT,$3,NIL); }
              ;

/* Numeric expression */
nexpr         : nterm { $$ = $1; }
              | number { $$ = $1; }
              | nexpr PLUS nexpr { $$ = new_node(PLUS,$1,$3); }
              | nexpr MINUS nexpr { $$ = new_node(MINUS,$1,$3); }
              | nexpr TIMES nexpr { $$ = new_node(TIMES,$1,$3); }
              | nexpr DIVIDE nexpr { $$ = new_node(DIVIDE,$1,$3); }
              | nexpr MOD nexpr { $$ = new_node(MOD,$1,$3); }
              ;

atomic_form   : FALSEEXP
              | TRUEEXP
              | nexpr EQUAL nexpr { $$ = new_node(EQUAL,$1,$3); }
              | nexpr NOTEQUAL nexpr { $$ = new_node(NOTEQUAL,$1,$3); }
              | nexpr LT nexpr { $$ = new_node(LT,$1,$3); }
              | nexpr GT nexpr { $$ = new_node(GT,$1,$3); }
              | nexpr LE nexpr { $$ = new_node(LE,$1,$3); }
              | nexpr GE nexpr { $$ = new_node(GE,$1,$3); }
              | nexpr SETIN setconst { $$ = new_node(SETIN,$1,$3); }
              | nexpr SETNOTIN setconst { $$ = new_node(NOT,new_node(SETIN,$1,$3),NIL); }
              | nterm { $$ = $1; }
              ;

functioncall  : ATOM LP exprlist RP { $$ = new_node(FUNC,$1,$3);}
              | ATOM NEXT_LTL { $$ = new_node(FUNC,$1,NIL);}
              ;

/* We have to leave expr this complex for backward compatibility. */
expr          : term
              | number
              | QUOTE
              | functioncall
	      | subrange
	      | FALSEEXP
	      | TRUEEXP
	      | LP expr RP { $$ = $2; }
	      | QUOTE_LP expr RP { $$ = new_node(QUOTE_LP, $2, NIL); }
	      | expr IMPLIES expr { $$ = new_node(IMPLIES,$1,$3); }
	      | expr IFF expr { $$ = new_node(IFF,$1,$3); }
	      | expr OR expr { $$ = new_node(OR,$1,$3); }
              | OR for_clause LCB expr RCB 
                  { $2->type = OR; $$ = new_node(FOR,$2,$4); }
              | AND for_clause LCB expr RCB 
                  { $2->type = AND; $$ = new_node(FOR,$2,$4); }
              | PLUS for_clause LCB expr RCB 
                  { $2->type = PLUS; $$ = new_node(FOR,$2,$4); }
	      | expr AND expr { $$ = new_node(AND,$1,$3); }
	      | NOT expr { $$ = new_node(NOT,$2,NIL); }
	      | expr FASTAND expr { $$ = new_node(FASTAND,$1,$3); }
	      | expr FORSOME expr { $$ = new_node(FORSOME,$3,$1); }
	      | expr FORALL expr { $$ = new_node(FORALL,$3,$1); }
              | CASE caselist ESAC { $$ = $2; }
              | expr QUESTION expr COLON expr 
                {$$ = new_node(CASE,
                               new_node(COLON,$1,$3),
                               new_node(CASE,
                                        new_node(COLON,new_true,$5),
                                        new_true ) ); }
              | NEXT expr { $$ = new_node(NEXT,$2,NIL); }
              | SAT  expr { $$ = new_node(SAT,$2,NIL); }
              | QUANT LP expr RP { $$ = new_node(QUANT,$3,NIL); }
              | SIZE LP expr RP { $$ = new_node(SIZE,$3,NIL); }
              | EXIST LP term RP { $$ = new_node(EXIST,$3,NIL); }
              | TNO term { $$ = new_node(TNO,$2,NIL); }
              | LTL LP ltl_formula RP { $$ = $3; }
              | CTL LP ctl_formula RP { $$ = $3; }
              | expr PLUS expr { $$ = new_node(PLUS,$1,$3); }
              | expr MINUS expr { $$ = new_node(MINUS,$1,$3); }
              | expr TIMES expr { $$ = new_node(TIMES,$1,$3); }
              | expr DIVIDE expr { $$ = new_node(DIVIDE,$1,$3); }
              | expr MOD expr { $$ = new_node(MOD,$1,$3); }
              | expr EQUAL expr { $$ = new_node(EQUAL,$1,$3); }
              | expr NOTEQUAL expr { $$ = new_node(NOTEQUAL,$1,$3); }
              | expr STRING_EQ expr { $$ = new_node(STRING_EQ,$1,$3); }
              | expr LT expr { $$ = new_node(LT,$1,$3); }
              | expr GT expr { $$ = new_node(GT,$1,$3); }
              | expr LE expr { $$ = new_node(LE,$1,$3); }
              | expr GE expr { $$ = new_node(GE,$1,$3); }
              | setconst { $$ = $1; }
              | expr UNION expr { $$ = new_node(UNION,$1,$3); }
              | expr SETIN expr { $$ = new_node(SETIN,$1,$3); }
              | expr SETNOTIN expr { $$ = new_node(NOT,new_node(SETIN,$1,$3),NIL); }
	      ;


ltl_formula   : ALWAYS        ltl_formula { $$ = new_node(ALWAYS,$2,NIL); }
              | NEXT_LTL      ltl_formula { $$ = new_node(NEXT_LTL,$2,NIL); }
              | EVENTUALLY    ltl_formula { $$ = new_node(EVENTUALLY,$2,NIL); }
              | HASALWAYSBEEN ltl_formula { $$ = new_node(HASALWAYSBEEN,$2,NIL); }
              | ONCE	      ltl_formula { $$ = new_node(ONCE,$2,NIL); }
              | PREVIOUSLY    ltl_formula { $$ = new_node(PREVIOUSLY,$2,NIL); }
              | WEAKPREVIOUS  ltl_formula { $$ = new_node(WEAKPREVIOUS,$2,NIL); }
              | ltl_formula LTLUNTIL   ltl_formula { $$ = new_node(LTLUNTIL,$1,$3); }
              | ltl_formula WAITINGFOR ltl_formula { $$ = new_node(WAITINGFOR,$1,$3); }
              | ltl_formula SINCE      ltl_formula { $$ = new_node(SINCE,$1,$3); }
              | ltl_formula BACKTO     ltl_formula { $$ = new_node(BACKTO,$1,$3); }
              | ltl_formula ENTAILS    ltl_formula { $$ = new_node(ENTAILS,$1,$3); }
              | ltl_formula CONGRUENT  ltl_formula { $$ = new_node(CONGRUENT,$1,$3); }
              | LP ltl_formula RP { $$ = $2; }
              | ATOM LP ltl_formula RP { $$ = new_node(FUNC,$1,cons($3,NIL)); }
	      | ltl_formula IMPLIES ltl_formula { $$ = new_node(IMPLIES,$1,$3); }
	      | ltl_formula IFF ltl_formula { $$ = new_node(IFF,$1,$3); }
	      | ltl_formula OR ltl_formula { $$ = new_node(OR,$1,$3); }
	      | ltl_formula AND ltl_formula { $$ = new_node(AND,$1,$3); }
	      | NOT ltl_formula { $$ = new_node(NOT,$2,NIL); }
              | atomic_form { $$ = $1; }
              ;


ctl_formula   : atomic_form { $$ = $1; }
              | EX ctl_formula { $$ = new_node(EX,$2,NIL); }
              | AX ctl_formula { $$ = new_node(AX,$2,NIL); }
              | EF ctl_formula { $$ = new_node(EF,$2,NIL); }
              | AF ctl_formula { $$ = new_node(AF,$2,NIL); }
              | EG ctl_formula { $$ = new_node(EG,$2,NIL); }
              | AG ctl_formula { $$ = new_node(AG,$2,NIL); }
	      | A LB ctl_formula UNTIL ctl_formula RB { $$ = new_node(AU,$3,$5); }
	      | E LB ctl_formula UNTIL ctl_formula RB { $$ = new_node(EU,$3,$5); }
	      | A LB ctl_formula BUNTIL subrange ctl_formula RB
                       { $$ = new_node(ABU,new_node(AU,$3,$6),$5); }
	      | E LB ctl_formula BUNTIL subrange ctl_formula RB
                       { $$ = new_node(EBU,new_node(EU,$3,$6),$5); }
              | EBF subrange ctl_formula { $$ = new_node(EBF,$3,$2); }
              | ABF subrange ctl_formula { $$ = new_node(ABF,$3,$2); }
              | EBG subrange ctl_formula { $$ = new_node(EBG,$3,$2); }
              | ABG subrange ctl_formula { $$ = new_node(ABG,$3,$2); }
	      | LP ctl_formula RP { $$ = $2; }
	      | ctl_formula IMPLIES ctl_formula { $$ = new_node(IMPLIES,$1,$3); }
	      | ctl_formula IFF ctl_formula { $$ = new_node(IFF,$1,$3); }
	      | ctl_formula OR ctl_formula { $$ = new_node(OR,$1,$3); }
	      | ctl_formula AND ctl_formula { $$ = new_node(AND,$1,$3); }
	      | NOT ctl_formula { $$ = new_node(NOT,$2,NIL); }
              ;

neatomset     : constant
              | neatomset COMMA constant {$$ = new_node(UNION,$1,$3);}
              ;

constant      : ATOM
              | number
	      | FALSEEXP
	      | TRUEEXP
              ;

caselist      : {$$=new_true;}
              | expr COLON expr SEMI caselist
                {
	          $$ = new_node(CASE,new_node(COLON,$1,$3),$5);
	        }
              ;

qualifiedatom : ATOM {$$ = find_atom($1);}
              | AND ATOM {$$ = find_node(INOUT,find_atom($2),NIL);}
              | QUOTECHAR ATOM {$$ = find_node(DEFINE,find_atom($2),NIL);}
              ;

qualifiedterm : term {$$ = $1;}
              | QUOTECHAR term {$$ = find_node(DEFINE,$2,NIL);}
              ;

neparamlist   : qualifiedatom {$$ = cons($1,NIL);}
              | qualifiedatom EQDEF expr
                {$$ = cons(new_default_param($1, $3), NIL);}
              | neparamlist COMMA qualifiedatom {$$ = cons($3,$1);}
              | neparamlist COMMA qualifiedatom EQDEF expr
                {$$ = cons(new_default_param($3, $5), $1);}
              ;

paramlist     : {$$ = NIL;}
              | neparamlist {$$ = $1;}
              ;

quotelist     : QUOTE {$$ = cons($1,NIL);}
              | QUOTE COMMA quotelist {$$ = cons($1,$3); }
              ;

tlvcaselist   : {$$ = NIL;}
              | DEFAULT COLON stmts
                {
	          $$ = new_node(DEFAULT,new_node(COLON,NIL,reverse($3)),NIL);
	        }
              | quotelist COLON stmts tlvcaselist
                {
	          $$ = new_node(CASE,new_node(COLON,$1,reverse($3)),$4);
	        }
              ;

/* If the stmt is a list, make sure to append it rather to stmts,
   rather than just add it */
stmts         : stmt       { $$ = $1->type != LIST ? new_node(LIST,$1,NIL) : $1 ;}
              | stmts stmt { $$ = $2->type != LIST ? new_node(LIST,$2,$1)
                                                   : append($2, $1) }
              ;

stmt          : basicstmt {$$ = $1;}
              | BREAK SEMI    { $$ = new_node(BREAK,NIL,NIL);}
              | CONTINUE SEMI { $$ = new_node(CONTINUE,NIL,NIL);}
              | FIX   LP expr RP stmts END { $$ = new_fix($3,reverse($5));}
              | TLVFOR LP ATOM SETIN expr THREEDOTS expr RP stmts END
                  { $$ = new_tlvfor($3,PLUS,$5,$7,reverse($9));}
              | TLVFOR LP ATOM SETIN REVERSE expr THREEDOTS expr RP stmts END
                  { $$ = new_tlvfor($3,MINUS,$6,$8,reverse($10));}
              | LOCAL term EQDEF expr SEMI { $$ = new_node(LOCAL,$2,$4); }
              | LOCAL term SEMI { $$ = new_node(LOCAL,$2,NIL); }
              | TLV_RETURN SEMI   { $$ = new_node(TLV_RETURN,NIL,NIL);}
              | TLV_RETURN expr SEMI   { $$ = new_node(TLV_RETURN,$2,NIL);}
              ;


/* These statements can also appear outside of scripts... */
basicstmt     : LET qualifiedterm EQDEF expr SEMI { $$ = new_node(LET,$2,$4); }
              | IF LP expr RP stmts END { $$ = new_tlv_if($3,reverse($5),NIL);}
              | IF LP expr RP stmts ELSE stmts END
                  { $$ = new_tlv_if($3,reverse($5),reverse($7) );}
              | WHILE LP expr RP stmts END { $$ = new_node(WHILE,$3,reverse($5));}
              | TLVCASE LP expr RP tlvcaselist END
                  { $$ = new_node(TLVCASE,$3,$5);}
              | PRINT neqexprlist SEMI {$$ = new_node(PRINT,$2,NIL);}
              | RUN ATOM exprlist SEMI { $$ = new_node(RUN,$2,$3);}
              | CALL ATOM LP exprlist RP SEMI { $$ = new_node(RUN,$2,$4);}
              | ATOM exprlist SEMI { $$ = new_node(RUN,$1,$2);}
              | DUMP term SEMI {$$ = new_node(DUMP,$2,new_node(LIST,NIL,NIL));}
              | DUMP term COMMA QUOTE SEMI {$$ = new_node(DUMP,$2,new_node(LIST,$4,NIL));}
              | DUMP term COMMA QUOTE COMMA term SEMI {$$ = new_node(DUMP,$2,new_node(LIST,$4,$6));}
              | SETTIME SEMI {$$ = new_node(SETTIME,NIL,NIL);}
              | CHKTIME SEMI {$$ = new_node(CHKTIME,NIL,NIL);}
              | EXIT { $$ = new_node(EXIT,NIL,NIL);}
              | EXIT expr { $$ = new_node(EXIT,$2 ,NIL);}
              | term COLON type SEMI {$$ = new_node(COLON,$1,$3);}
              | error SEMI {$$ = iparse_tree = FAILURE_NODE; yyerrok; YYABORT; }
              | error END {$$ = iparse_tree = FAILURE_NODE; yyerrok; YYABORT; }
              ;

/*: command               {if (do_prompt) set_prompt();} */
commandlist   : istmtlist basicstmt  { $$ = $2; }
              | istmtlist { $$ = NIL;}
              ;

istmtlist     : istmtlist istmt   {if (do_prompt) set_prompt();}
              |
              ;

/* Interactive statement.  They are handled immediately, so they do
   not construct a parse tree. */
/*              | LOAD QUOTE SEMI { catch_err(load_file($2))}  */
istmt         : TO ATOM paramlist SEMI stmts END {catch_err(to_command($2,$3,reverse($5)))}
              | PROC ATOM LP paramlist RP SEMI stmts END {catch_err(to_command($2,$4,reverse($7)))}
              | PROC ATOM NEXT_LTL SEMI stmts END {catch_err(to_command($2,NIL,reverse($5)))}
              | FUNC ATOM LP paramlist RP SEMI stmts END {catch_err(func_command($2,$4,reverse($7),0))}
              | FUNC ATOM NEXT_LTL SEMI stmts END {catch_err(func_command($2,NIL,reverse($5),0))}
              | FUNC QUOTECHAR ATOM LP paramlist RP SEMI stmts END {catch_err(func_command($3,$5,reverse($8),1))}
              | FUNC QUOTECHAR ATOM NEXT_LTL SEMI stmts END {catch_err(func_command($3,NIL,reverse($6),1))}
              | SIZE term SEMI {catch_err(size_command($2))}
              ;

/*
command       : PRINT neqexprlist SEMI {catch_err(print_command($2))}
              | LET qualifiedterm EQDEF expr SEMI {catch_err(assign_command($2,$4))}
              | RUN ATOM exprlist SEMI {catch_err(run_command($2,$3))}
              | ATOM exprlist SEMI { catch_err(run_command($1,$2))}
              | CALL ATOM LP exprlist RP SEMI {catch_err(run_command($2,$4))}
              | DUMP term SEMI {catch_err(dump_command($2,NIL,NIL))}
              | DUMP term COMMA QUOTE SEMI {catch_err(dump_command($2,$4,NIL))}
              | DUMP term COMMA QUOTE COMMA term SEMI {catch_err(dump_command($2,$4,$6))}
              | SETTIME SEMI {catch_err(settime_command())}
              | CHKTIME SEMI {catch_err(chktime_command())}
              | istmt {}
              | error SEMI {yyerrok;}
              ; */
%%

