#include "lexer.h"
#include <cctype>

Lexer::Lexer(const std::string& src) : input(src), position(0) {}

char Lexer::peek() {
    return position < input.size() ? input[position] : '\0';
}

char Lexer::consume() {
    return position < input.size() ? input[position++] : '\0';
}

void Lexer::skipWhitespace() {
    while (isspace(peek())) consume();
}

Token Lexer::nextToken() {
    skipWhitespace();
    char c = peek();
    if (c == '\0') return Token{END, ""};

    if (isalpha(c)) {
        std::string value;
        while (isalnum(peek())) value += consume();
        if (value == "int" || value == "printf" || value == "return" ||
            value == "if" || value == "else" || value == "while" || value == "for") {
            return Token{KEYWORD, value};
        }
        return Token{IDENTIFIER, value};
    }

    if (isdigit(c)) {
        std::string value;
        while (isdigit(peek())) value += consume();
        return Token{NUMBER, value};
    }

    if (c == '"') {
        consume();
        std::string value;
        while (peek() != '"') value += consume();
        consume();
        return Token{STRING, value};
    }

    std::string op(1, consume());
    if (position < input.size()) {
        char next_c = input[position];
        std::string multi_op = op + next_c;
        if (multi_op == "&&" || multi_op == "||" || multi_op == "==" ||
            multi_op == "!=" || multi_op == "<=" || multi_op == ">=") {
            op += next_c;
            consume();
        }
    }
    return Token{OPERATOR, op};
}

std::vector<Token> Lexer::tokenize() {
    std::vector<Token> tokens;
    while (true) {
        Token token = nextToken();
        if (token.type == END) break;
        tokens.push_back(token);
    }
    return tokens;
}

