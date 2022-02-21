%{
#include <string.h>
#include <stdio.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <errno.h>
int numChars = 0, numWords = 0, numLines = 0;
int comment = 0, cnt = 0, func = 0;
%}

TYPEID      "Int"|"Float"|"String"|"Bool"|"Void"
KEYWORD     "fprintf"|"while"|"aafor"|"if"|"else"|"continue"|"break"|"return"
BRACKETS    ";"|":"|"{"|"}"|"("|")"|"["|"]"|"%f"|"%s"|"%lld"
OPERATOR    "+"|"-"|"*"|"/"|"%"|"&"|"|"|"^"|"~"|":="|">"|">="|"=="|"!="|"<="|"<"|"&&"|"||"|"!"
SYMBOL      {OPERATOR}|{BRACKETS}
NUMBER      [0-9]+("."[0-9]*)?
VARIABLE    [a-z][0-9a-zA-Z_]*
FUNCTION    "func"
BLANK       [ \t\n]+
WORDS       [^ \t\n]+

%%
{BLANK}     { if (cnt) numChars += yyleng, cnt = 0; REJECT; }
{WORDS}     { if (!cnt) { numChars += yyleng, numWords++, cnt = 1; if (numLines == 0 && comment) printf("%s\n",yytext);} REJECT; }
#   { if (numLines == 0 && !comment) printf("#name "); comment = 1; }
\n  { numLines++; comment = 0; }
{FUNCTION}  { if (!comment) func = 1; }
{NUMBER}    { if (!comment) printf("#%d CONST %s\n", numLines, yytext); }
{SYMBOL}    { if (!comment) printf("#%d %s\n", numLines, yytext); }
{TYPEID}    { if (!comment) printf("#%d TYPEID %s\n", numLines, yytext); }
{KEYWORD}   { if (!comment) printf("#%d KEYWORD %s\n", numLines, yytext); }
{VARIABLE}  { if (func) { printf("#%d func %s\n", numLines, yytext); func = 0; }
              else if (strcmp(yytext,"stdout")!=0 && strcmp(yytext,"stderr")!=0)
                   if (!comment) printf("#%d OBJECTED %s\n", numLines, yytext); }
.   
%%
int yywarp() {
    return 1;
}

int main() {
	yylex();
	printf("lines:%d,words:%d,chars:%d\n", numLines, numWords, numChars);
	return 0;
}