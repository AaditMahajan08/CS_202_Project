# C to Promela Compiler

This project provides two different compiler implementations to translate C code into Promela code. Both use a lexer and parser to perform the conversion:

- **Project_CPP**: Implements the lexer and parser manually in C++.
- **Project_Lex_Yacc**: Uses Lex and Yacc to automatically generate the lexer and parser.

## Directory Structure

```
Project_CPP/
├── lexer.cpp
├── lexer.h
├── main.cpp
├── parser.cpp
└── parser.h

Project_Lex_Yacc/
├── lexer.l
└── parser.y
```

## Compilation Instructions

### Lex/Yacc Implementation

Make sure you have `flex`, `bison`, and `gcc` installed.

```
bison -d Project_Lex_Yacc/parser.y -o c_parser.tab.c
flex -o lex.yy.c Project_Lex_Yacc/lexer.l
gcc -c c_parser.tab.c
gcc -c lex.yy.c
gcc -o c2promela c_parser.tab.o lex.yy.o -lfl
```

Run:
```
./c2promela < input.c > output.pml
```

### C++ Implementation

Make sure you have `g++` installed.

```
g++ -o c2promela_cpp Project_CPP/main.cpp Project_CPP/lexer.cpp Project_CPP/parser.cpp
```

Run:
```
./c2promela_cpp < input.c > output.pml
```

## Description

Both implementations achieve the same goal: converting C code into Promela for formal analysis or further processing. You can choose either approach depending on your preference for a hand-written or tool-generated lexer and parser.

## Requirements

- `flex`, `bison`, `gcc` (for Lex/Yacc implementation)
- `g++` (for C++ implementation)
