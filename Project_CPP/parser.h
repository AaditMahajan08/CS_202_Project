#ifndef PARSER_H
#define PARSER_H

#include <vector>
#include <fstream>
#include "lexer.h"

class Parser {
    std::vector<Token> tokens;
    size_t current;
    std::ofstream output;
    
    void parseDeclaration();
    void parseAssignment();
    void parsePrint();
    void parseConditional();
    void parseLoop();
    void parseFunction();
    
public:
    Parser(const std::vector<Token>& tokens, const std::string& filename);
    void parse();
};

#endif
