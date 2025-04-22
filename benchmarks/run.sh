#!/bin/bash
# Run script for Homework 2 CSE 583 Winter 2025
# Place this script in the benchmarks folder and run it using the name of the file (without the file type)
# e.g. sh run.sh hw2correct1

# ACTION NEEDED: If the path is different, please update it here.
PATH2LIB="../build/obfuscationPass/ObfuscationPass.so"        # Specify your build directory in the project

# ACTION NEEDED: Choose the correct pass when running.
PASS=${2}

rm -f default.profraw *_prof *_obfuscation *.bc *.profdata *_output *.ll

clang -emit-llvm -c ${1}.c -Xclang -O0 -fno-optimize-sibling-calls -o ${1}.bc

opt -load-pass-plugin="${PATH2LIB}" -passes="${PASS}" ${1}.bc -o ${1}.obfuscation.bc > /dev/null

# Generate binary excutable before FPLICM: Unoptimzed code
clang ${1}.bc -o ${1}_no_obfuscation
# Generate binary executable after FPLICM: Optimized code
clang ${1}.obfuscation.bc -o ${1}_obfuscation

# Produce output from binary to check correctness
./${1}_no_obfuscation > correct_output
./${1}_obfuscation > obfuscation_output

echo -e "\n=== Program Correctness Validation ==="
if [ "$(diff correct_output obfuscation_output)" != "" ]; then
    echo -e ">> Outputs do not match\n"
else
    echo -e ">> Outputs match\n"
fi

# Cleanup: Remove this if you want to retain the created files (for example, for viz.sh). 
# And you do need to.
# rm -f *.bc
