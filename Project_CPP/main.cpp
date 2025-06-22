#include <iostream>
#include <fstream>
#include "lexer.h"
#include "parser.h"

std::string readFile(const std::string& filename) {
    std::ifstream file(filename);
    return std::string((std::istreambuf_iterator<char>(file)),
                      std::istreambuf_iterator<char>());
}

int main() {
    std::string input = readFile("input.c");
    Lexer lexer(input);
    std::vector<Token> tokens = lexer.tokenize();

    Parser parser(tokens, "output.pml");
    parser.parse();

    std::cout << "Translation completed. Output written to output.pml\n";
    return 0;
}

