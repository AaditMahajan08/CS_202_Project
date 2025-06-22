#include "parser.h"
#include <iostream>

Parser::Parser(const std::vector<Token>& t, const std::string& filename)
    : tokens(t), current(0), output(filename) {}

void Parser::parseDeclaration() {
    current++;
    std::string name = tokens[current++].value;
    output << "    int " << name;

    if (tokens[current].value == "=") {
        current++;
        output << " = ";
        while (tokens[current].value != ";") {
            output << tokens[current].value;
            current++;
        }
    }
    output << ";\n";
    current++;
}

void Parser::parseAssignment() {
    std::string name = tokens[current++].value;
    current++;
    output << "    " << name << " = ";
    
    while (tokens[current].value != ";") {
        output << tokens[current].value;
        current++;
    }
    output << ";\n";
    current++;
}

void Parser::parsePrint() {
    current += 2;
    std::string format = tokens[current++].value;
    current++;
    std::string var = tokens[current++].value;
    current += 2;
    output << "    printf(\"" << format << "\", " << var << ");\n";
}

void Parser::parseConditional() {
    bool isFirstCondition = true;
    bool hasElse = false;

    while (true) {
        if (tokens[current].value == "if" || tokens[current].value == "else") {
            if (tokens[current].value == "else") {
                current++;
                if (current >= tokens.size()) break;
                if (tokens[current].value != "if") {
                    output << "    :: else -> {\n";
                    if (tokens[current].value == "{") {
                        current++;
                        while (tokens[current].value != "}") {
                            if (tokens[current].type == KEYWORD) {
                                std::string kw = tokens[current].value;
                                if (kw == "int") parseDeclaration();
                                else if (kw == "printf") parsePrint();
                                else if (kw == "if") parseConditional();
                                else if (kw == "while") parseLoop();
                                else current++;
                            }
                            else if (tokens[current].type == IDENTIFIER) parseAssignment();
                            else current++;
                        }
                        current++;
                    }
                    output << "    }\n";
                    hasElse = true;
                    break;
                }
                // Handle "else if"
                current++; // skip "if"
            }
            else {
                current++; // skip "if"
            }

            if (isFirstCondition) {
                output << "    if\n";
                isFirstCondition = false;
            }

            current++; // skip '('
            std::string condition;
            while (tokens[current].value != ")") {
                condition += tokens[current].value;
                current++;
            }
            current++; // skip ')'
            output << "    :: (" << condition << ") -> {\n";

            if (tokens[current].value == "{") {
                current++;
                while (tokens[current].value != "}") {
                    if (tokens[current].type == KEYWORD) {
                        std::string kw = tokens[current].value;
                        if (kw == "int") parseDeclaration();
                        else if (kw == "printf") parsePrint();
                        else if (kw == "if") parseConditional();
                        else if (kw == "while") parseLoop();
                        else current++;
                    }
                    else if (tokens[current].type == IDENTIFIER) parseAssignment();
                    else current++;
                }
                current++;
            }
            else {
                // Handle single statements without braces
                if (tokens[current].type == KEYWORD && tokens[current].value == "printf") {
                    parsePrint();
                }
            }
            output << "    }\n";
        }
        else {
            break;
        }
    }

    if (!hasElse && !isFirstCondition) {
        output << "    :: else -> {\n";
        output << "    }\n";
    }

    if (!isFirstCondition) {
        output << "    fi;\n";
    }
}

void Parser::parseLoop() {
    current++; // Skip 'while'
    current++; // Skip '('
    std::string condition;
    while (tokens[current].value != ")") {
        condition += tokens[current].value;
        current++;
    }
    current++; // Skip ')'
    output << "    do\n";
    output << "    :: (" << condition << ") -> {\n";
    
    if (tokens[current].value == "{") {
        current++;
        while (tokens[current].value != "}") {
            if (tokens[current].type == KEYWORD) {
                std::string kw = tokens[current].value;
                if (kw == "int") parseDeclaration();
                else if (kw == "printf") parsePrint();
                else if (kw == "if") parseConditional();
                else if (kw == "while") parseLoop();
                else current++;
            }
            else if (tokens[current].type == IDENTIFIER) parseAssignment();
            else current++;
        }
        current++;
    }
    output << "    }\n";
    output << "    :: else -> break;\n";
    output << "    od;\n";
}

void Parser::parseFunction() {
    current++; // Skip 'int'
    std::string funcName = tokens[current++].value;
    current += 3; // Skip '(', ')', and '{'
    output << "proctype " << funcName << "() {\n";
    
    while (tokens[current].value != "}") {
        if (tokens[current].type == KEYWORD) {
            std::string kw = tokens[current].value;
            if (kw == "int") {
                if (tokens[current+2].value == "(") parseFunction();
                else parseDeclaration();
            }
            else if (kw == "printf") parsePrint();
            else if (kw == "if") parseConditional();
            else if (kw == "while") parseLoop();
            else current++;
        }
        else if (tokens[current].type == IDENTIFIER) parseAssignment();
        else current++;
    }
    output << "}\n";
    current++;
}

void Parser::parse() {
    output << "init {\n";
    while (current < tokens.size()) {
        if (tokens[current].type == KEYWORD) {
            std::string kw = tokens[current].value;
            if (kw == "int") {
                if (current+2 < tokens.size() && tokens[current+2].value == "(") {
                    parseFunction();
                } else {
                    parseDeclaration();
                }
            }
            else if (kw == "printf") parsePrint();
            else if (kw == "if") parseConditional();
            else if (kw == "while") parseLoop();
            else current++;
        }
        else if (tokens[current].type == IDENTIFIER) parseAssignment();
        else current++;
    }
    output << "}\n";
    output.close();
}
