#ifndef LEXER_H
#define LEXER_H

#include <string>
#include <vector>

enum TokenType {
    KEYWORD,
    IDENTIFIER,
    NUMBER,
    OPERATOR,
    STRING,
    END
};

struct Token {
    TokenType type;
    std::string value;
};

class Lexer {
    std::string input;
    size_t position;
    
    char peek();
    char consume();
    void skipWhitespace();
    
public:
    Lexer(const std::string& src);
    Token nextToken();
    std::vector<Token> tokenize();
};

#endif
