// Test Case which goes through many different type of string stuff
// Intended as a stress test to our obfuscation

#include <stdio.h>
#include <stdint.h>
#include <string.h>

char str1[] = "Hello, World!";
char str2[] = "";
char str3[] = "Hello, World!2";
char a = 'a';

int main() {
    
    // Test #1
    printf("%s\n", str1);
    // printf("%s\n", str1);

    return 0;
}