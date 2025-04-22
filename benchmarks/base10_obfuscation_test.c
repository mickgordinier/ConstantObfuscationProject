// Test Case which goes through many different type of digit level obfuscation stuff
// Intended as a stress test to our obfuscation

#include <stdio.h>
#include <stdint.h>

// All variables declared as global constants to be picked by the LLVM pass
int CONST_SINGLE_DIGIT = 5;
int CONST_REPEATED_DIGITS = 1111;  // Used inside main
int CONST_ALL_DIGITS = 1234567890;
int CONST_TRAILING_ZEROS = 1000;
int CONST_ZERO = 0;
int CONST_INT_MAX = 2147483647;
int CONST_INT_MIN = -2147483648;
int CONST_NEGATIVE = -12345;
int CONST_EXPRESSION = 1234 + 5678;
int CONST_UNUSED = 9999; // intentionally unused
int64_t CONST_INT64_MAX = 9223372036854775807;
int64_t CONST_INT64_MIN = -9223372036854775807 - 1;

void run_tests() {
    printf("Testing Digit-Level Constant Obfuscation\n");

    printf("Single Digit        : %d\n", CONST_SINGLE_DIGIT);         // Expect 5
    printf("Repeated Digits     : %d\n", CONST_REPEATED_DIGITS);      // Expect 1111
    printf("All Digits          : %d\n", CONST_ALL_DIGITS);           // Expect 1234567890
    printf("Trailing Zeros      : %d\n", CONST_TRAILING_ZEROS);       // Expect 1000
    printf("Zero                : %d\n", CONST_ZERO);                 // Expect 0
    printf("INT_MAX             : %d\n", CONST_INT_MAX);              // Expect 2147483647
    printf("INT_MIN             : %d\n", CONST_INT_MIN);              // Expect -2147483648
    printf("Negative Constant   : %d\n", CONST_NEGATIVE);             // Expect -12345
    printf("Expression Constant : %d\n", CONST_EXPRESSION);           // Expect 6912
    printf("INT64_MAX           : %ld\n", CONST_INT64_MAX);           // Expect 9223372036854775807
    printf("INT64_MIN           : %ld\n", CONST_INT64_MIN);           // Expect -9223372036854775808
}

int main() {
    int usedInMain = CONST_REPEATED_DIGITS + 10;
    printf("Used in main        : %d\n", usedInMain);                 // Expect 1121
    run_tests();
    return 0;
}
