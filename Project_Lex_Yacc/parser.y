%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

FILE *out;
int yylex();
void yyerror(const char *s) {
    fprintf(stderr, "Error: %s\n", s);
}
%}

%define parse.error verbose

%union {
    char* str;
}

/* Terminals with string values */
%token <str> INT_NUM FLOAT_NUM ID
%token INT FLOAT VOID IF ELSE FOR WHILE RETURN
%token EQ NE LE GE LT GT ASSIGN PLUS MINUS MUL DIV MOD AND OR NOT
%token SEMICOLON COMMA LPAREN RPAREN LBRACE RBRACE

/* Non-terminals returning strings */
%type <str> expr type

%left OR
%left AND
%left EQ NE
%left LT GT LE GE
%left PLUS MINUS
%left MUL DIV MOD
%right NOT
%right ASSIGN

%%
program:
    functions
    ;

functions:
    function
    | functions function
    ;

function:
    type ID LPAREN params RPAREN compound_stmt
    {
        /* Print Promela proctype or init */
        if (strcmp($2, "main") == 0) {
            fprintf(out, "init ");
        } else {
            fprintf(out, "proctype %s ", $2);
        }
        free($1);
        free($2);
        /* compound_stmt will print the { and } */
    }
    ;

params:
    /* empty */
    | VOID
    | param_list
    ;

param_list:
    param
    | param_list COMMA param
    ;

param:
    type ID
    {
        free($1);
        free($2);
    }
    ;

type:
      INT   { $$ = strdup("int"); }
    | FLOAT { $$ = strdup("float"); }
    | VOID  { $$ = strdup("void"); }
    ;

compound_stmt:
    LBRACE
        { fprintf(out, "{\n"); }
    stmts
    RBRACE
        { fprintf(out, "}\n"); }
    ;

stmts:
    /* empty */
    | stmts stmt
    ;

stmt:
    expr_stmt
    | type ID SEMICOLON   { /* skip declaration */ free($1); free($2); }
    | type ID ASSIGN expr SEMICOLON   { fprintf(out, "%s = %s;\n", $2, $4); free($1); free($2); free($4); }
    | if_stmt
    | while_stmt
    | for_stmt
    | return_stmt
    | compound_stmt
    ;

expr_stmt:
    expr SEMICOLON   { fprintf(out, "%s;\n", $1); free($1); }
    | SEMICOLON      { /* skip empty statement */ }
    ;

return_stmt:
    RETURN expr SEMICOLON
    {
        /* 'return' in Promela we treat as a skip */
        fprintf(out, "skip; /* %s */\n", $2);
        free($2);
    }
    ;

if_stmt:
    IF LPAREN expr RPAREN
    {
        fprintf(out, "if\n :: (%s) ->\n", $3);
        free($3);
    }
    stmt
    else_clause
    ;

else_clause:
    ELSE
    {
        fprintf(out, " :: else ->\n");
    }
    stmt
    {
        fprintf(out, "fi;\n");
    }
  | /* empty */
    {
        fprintf(out, " :: else -> skip\nfi;\n");
    }
    ;

while_stmt:
    WHILE LPAREN expr RPAREN
    {
        fprintf(out, "do\n :: (%s) ->\n", $3);
        free($3);
    }
    stmt
    {
        fprintf(out, " :: else -> break;\nod;\n");
    }
    ;

for_stmt:
    FOR LPAREN expr SEMICOLON expr SEMICOLON expr RPAREN stmt
    {
        /* $3=init, $5=condition, $7=incr */
        fprintf(out, "%s;\n", $3);
        fprintf(out, "do\n :: (%s) ->\n", $5);
        free($3); free($5);
        fprintf(out, "   %s;\n", $7);
        fprintf(out, " :: else -> break;\n od;\n");
        free($7);
    }
    ;

expr:
      ID ASSIGN expr
        {
            /* assignment */
            size_t n = strlen($1) + strlen($3) + 4;
            $$ = malloc(n);
            snprintf($$, n, "%s = %s", $1, $3);
            free($1); free($3);
        }
    | expr PLUS expr
        {
            size_t n = strlen($1) + strlen($3) + 4;
            $$ = malloc(n);
            snprintf($$, n, "%s + %s", $1, $3);
            free($1); free($3);
        }
    | expr MINUS expr
        {
            size_t n = strlen($1) + strlen($3) + 4;
            $$ = malloc(n);
            snprintf($$, n, "%s - %s", $1, $3);
            free($1); free($3);
        }
    | expr MUL expr
        {
            size_t n = strlen($1) + strlen($3) + 4;
            $$ = malloc(n);
            snprintf($$, n, "%s * %s", $1, $3);
            free($1); free($3);
        }
    | expr DIV expr
        {
            size_t n = strlen($1) + strlen($3) + 4;
            $$ = malloc(n);
            snprintf($$, n, "%s / %s", $1, $3);
            free($1); free($3);
        }
    | expr MOD expr
        {
            size_t n = strlen($1) + strlen($3) + 4;
            $$ = malloc(n);
            snprintf($$, n, "%s %% %s", $1, $3);
            free($1); free($3);
        }
    | expr EQ expr
        {
            size_t n = strlen($1) + strlen($3) + 5;
            $$ = malloc(n);
            snprintf($$, n, "%s == %s", $1, $3);
            free($1); free($3);
        }
    | expr NE expr
        {
            size_t n = strlen($1) + strlen($3) + 5;
            $$ = malloc(n);
            snprintf($$, n, "%s != %s", $1, $3);
            free($1); free($3);
        }
    | expr LE expr
        {
            size_t n = strlen($1) + strlen($3) + 5;
            $$ = malloc(n);
            snprintf($$, n, "%s <= %s", $1, $3);
            free($1); free($3);
        }
    | expr GE expr
        {
            size_t n = strlen($1) + strlen($3) + 5;
            $$ = malloc(n);
            snprintf($$, n, "%s >= %s", $1, $3);
            free($1); free($3);
        }
    | expr LT expr
        {
            size_t n = strlen($1) + strlen($3) + 4;
            $$ = malloc(n);
            snprintf($$, n, "%s < %s", $1, $3);
            free($1); free($3);
        }
    | expr GT expr
        {
            size_t n = strlen($1) + strlen($3) + 4;
            $$ = malloc(n);
            snprintf($$, n, "%s > %s", $1, $3);
            free($1); free($3);
        }
    | expr AND expr
        {
            size_t n = strlen($1) + strlen($3) + 5;
            $$ = malloc(n);
            snprintf($$, n, "%s && %s", $1, $3);
            free($1); free($3);
        }
    | expr OR expr
        {
            size_t n = strlen($1) + strlen($3) + 4;
            $$ = malloc(n);
            snprintf($$, n, "%s || %s", $1, $3);
            free($1); free($3);
        }
    | NOT expr
        {
            size_t n = strlen($2) + 3;
            $$ = malloc(n);
            snprintf($$, n, "!(%s)", $2);
            free($2);
        }
    | LPAREN expr RPAREN
        {
            size_t n = strlen($2) + 3;
            $$ = malloc(n);
            snprintf($$, n, "(%s)", $2);
            free($2);
        }
    | ID
        {
            $$ = strdup($1);
            free($1);
        }
    | INT_NUM
        {
            $$ = strdup($1);
            free($1);
        }
    | FLOAT_NUM
        {
            $$ = strdup($1);
            free($1);
        }
    ;
%%
int main(int argc, char *argv[]) {
    out = fopen("output.pml", "w");
    if (!out) { perror("output.pml"); return 1; }
    yyparse();
    fclose(out);
    return 0;
}

