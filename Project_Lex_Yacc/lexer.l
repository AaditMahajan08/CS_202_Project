%{
#include "parser.tab.h"
#include <stdlib.h>
#include <string.h>
%}

DIGIT       [0-9]
ID_START    [a-zA-Z_]
ID_CHAR     [a-zA-Z0-9_]

%%
"int"       { yylval.str = strdup("int"); return INT; }
"float"     { yylval.str = strdup("float"); return FLOAT; }
"void"      { yylval.str = strdup("void"); return VOID; }

"if"        { return IF; }
"else"      { return ELSE; }
"while"     { return WHILE; }
"for"       { return FOR; }
"return"    { return RETURN; }

"=="        { return EQ; }
"!="        { return NE; }
"<="        { return LE; }
">="        { return GE; }
"<"         { return LT; }
">"         { return GT; }

"&&"        { return AND; }
"||"        { return OR; }
"!"         { return NOT; }

"="         { return ASSIGN; }
"+"         { return PLUS; }
"-"         { return MINUS; }
"*"         { return MUL; }
"/"         { return DIV; }
"%"         { return MOD; }

"("         { return LPAREN; }
")"         { return RPAREN; }
"{"         { return LBRACE; }
"}"         { return RBRACE; }
";"         { return SEMICOLON; }
","         { return COMMA; }

{DIGIT}+"."{DIGIT}*  { yylval.str = strdup(yytext); return FLOAT_NUM; }
{DIGIT}+            { yylval.str = strdup(yytext); return INT_NUM; }
{ID_START}{ID_CHAR}* { yylval.str = strdup(yytext); return ID; }

[ \t\r\n]+          { /* skip whitespace */ }
.                   { printf("Unknown character: %s\n", yytext); }

%%

int yywrap() {
    return 1;
}

