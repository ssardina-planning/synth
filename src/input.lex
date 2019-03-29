%{

/* This file contains all tokens both for smv and tlv-basic  */


#include <node.h>

/* Read interactive input using gnu readline. */
#include "myread.h"

#include <y.tab.h>
#include <util_err.h>



/* This routine is called by yacc when a syntax error occurs */
/*int yyerror(const char *s) */
int yyerror(char *s)
{
#if LEX == flex
    extern char *yytext;
#else
    extern char yytext[];
#endif
    extern int loading_smv_file;

    start_err();
    fprintf(tlvstderr,"at token \"%s\": %s\n",yytext,s);

    /* In loading an smv file then terminate. */
    if(loading_smv_file) finish_err();
}


/* "Load"                  return(LOAD); */

int yywrap(void)
{
  return(1);
}

%}
%a	15000
%o	27000
%p      2800
%%
[ \n\t]                 ;
"--".*\n                ;
">>"                    ;
"#".*\n               { extern int yylineno;
                        sscanf(yytext,"# %d",&yylineno);
                      }

"ltl" { return LTL; }
"ctl" { return CTL; }

"()"  	 	{ return NEXT_LTL; }
"<>"		{ return EVENTUALLY; }
"[]"		{ return ALWAYS; }
"(~)"		{ return WEAKPREVIOUS; }
"(_)"		{ return PREVIOUSLY; }
"<_>"		{ return ONCE; }
"[_]"		{ return HASALWAYSBEEN; }
"Until"		{ return LTLUNTIL; }
"Awaits"	{ return WAITINGFOR; }
"Since"		{ return SINCE; }
"Backto"	{ return BACKTO; }
"<==>"		{ return CONGRUENT; }
"==>"		{ return ENTAILS; }

"=="                    return STRING_EQ;

"|||"           { return SYNCHCOMP; }
"||"            { return ASYNCHCOMP; }

"COMPOSED"     { return STRUCTURE; }
"OWNED"         { return OWNED;}
"MODULE"                return(MODULE);
"process"               return(PROCESS);
"system"                return(SYSTEM);
"DEFINE"                return(DEFINE);
"VAR"                   return(VAR);
"CONSTANT"              return(CONSTANT);
"INIT"                  return(INIT);
"TRANS"                 return(TRANS);
"SPEC"                  return(SPEC);
"FAIRNESS"              return(FAIRNESS);
"ISA"                   return(ISA);
"ASSIGN"                return(ASSIGN);
"INPUT"                 return(INPUT);
"OUTPUT"                return(OUTPUT);
"IMPLEMENTS"            return(IMPLEMENTS);
"GOTO"                  return(GOTO);
"JUSTICE"               return(JUSTICE);
"COMPASSION"            return(COMPASSION);
"size"                  return(SIZE);
"Dump"                  return(DUMP);
"sat"                   return(SAT);
"quant"                 return(QUANT);
"exist"                 return(EXIST);
"tno"                   return(TNO);
"Let"                   return(LET);
"Local"                 return(LOCAL);
"While"                 return(WHILE);
"Fix"                   return(FIX);
"For"                   return(TLVFOR);
"To"                    return(TO);
"Run"                   return(RUN);
"End"                   return(END);
"If"                    return(IF);
"if"                    return(IFSMV);
"Else"                  return(ELSE);
"else"                  return(ELSESMV);
"Break"                 return(BREAK);
"Return"                return(TLV_RETURN);
"Continue"              return(CONTINUE);
"Print"                 return(PRINT);
"Settime"               return(SETTIME);
"Chktime"               return(CHKTIME);
"forsome"               return(FORSOME);
"forall"                return(FORALL);
"for"                   return(FOR);
"Func"                  return(FUNC);
"Proc"                  return(PROC);
"Call"                  return(CALL);
"array"                 return(ARRAY);
"kind"                  return(KIND);
"of"                    return(OF);
"boolean"               return(BOOLEAN);
"reverse"               return(REVERSE);
"EX"                    return(EX);
"AX"                    return(AX);
"EF"                    return(EF);
"AF"                    return(AF);
"EG"                    return(EG);
"AG"                    return(AG);
"E"                     return(E);
"A"                     return(A);
"U"                     return(UNTIL);
"BU"                    return(BUNTIL);
"EBF"                   return(EBF);
"ABF"                   return(ABF);
"EBG"                   return(EBG);
"ABG"                   return(ABG);
"("                     return(LP);
")"                     return(RP);
"["                     return(LB);
"]"                     return(RB);
"{"                     return(LCB);
"}"                     return(RCB);
"FALSE"                 {
				yylval.node = new_node(FALSEEXP,NIL,NIL);
				return(FALSEEXP);
			}
"TRUE"                  {
				yylval.node = new_node(TRUEEXP,NIL,NIL);
				return(TRUEEXP);
			}
"case"                  return(CASE);
"Case"                  return(TLVCASE);
"default"               return(DEFAULT);
"esac"                  return(ESAC);
":="                    return(EQDEF);
"&"                     return(AND);
"/\\"                   return(AND);
"|"                     return(OR);
"\\/"                   return(OR);
"+"                     return(PLUS);
"-"                     return(MINUS);
"*"                     return(TIMES);
"/"                     return(DIVIDE);
"mod"                   return(MOD);
"!="                    return(NOTEQUAL);
"="                     return(EQUAL);
"<="                    return(LE);
">="                    return(GE);
"<"                     return(LT);
">"                     return(GT);
[qQ]uit                 return(EXIT);
[eE]xit                 return(EXIT);
"next"                  return(NEXT);
"init"                  return(SMALLINIT);
"self"                  return(SELF);
"union"                 return(UNION);
"in"                    return(SETIN);
"notin"                 return(SETNOTIN);
"..."                   return(THREEDOTS);
".."                    return(TWODOTS);
"."                     return(DOT);
"->"                    return(IMPLIES);
"<->"                   return(IFF);
"&&&"                   return(FASTAND);
"!"                     return(NOT);
"'("                    return(QUOTE_LP);
"'"                     return(QUOTECHAR);
[A-Za-z_][A-Za-z0-9_\$#-]*  { 
                             yylval.node = new_string_node(ATOM,yytext,NIL);
                             return(ATOM);
                           }
[0-9]+                  {
                          int i;
                          sscanf(yytext,"%d",&i);
                          yylval.node = new_NUMBER_node(i);
                          return(NUMBER);
                        }
\"[^\"\n]*\"              {
                          /* The token is a quoted string */
                          yytext[strlen(yytext)-1]=0;
                          yylval.node = new_string_node(QUOTE,yytext+1,NIL);
                             return(QUOTE);
                        }
","                     return(COMMA);
":"                     return(COLON);
";"                     return(SEMI);
"\?"                     return(QUESTION);
%%

