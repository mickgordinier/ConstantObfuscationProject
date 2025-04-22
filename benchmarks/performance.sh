#!/bin/bash
# Usage: sh performance.sh filename passname
# Example: sh performance.sh hw2correct1 fplicm

# Set plugin path
PATH2LIB="../build/obfuscationPass/ObfuscationPass.so"

# Inputs
FILE=$1
PASS=$2


rm -f *_obfuscation *_no_obfuscation *.bc *.profdata *.ll *.s perf_output.txt
echo -e "\n>>> Building binaries for performance evaluation"
# Compile to LLVM IR
clang -emit-llvm -c ${FILE}.c -Xclang -O0 -fno-optimize-sibling-calls -o ${FILE}.bc
# Apply obfuscation pass
opt -load-pass-plugin="${PATH2LIB}" -passes="${PASS}" ${FILE}.bc -o ${FILE}.obfuscation.bc > /dev/null
# Generate executables
clang ${FILE}.bc -o ${FILE}_no_obfuscation
clang ${FILE}.obfuscation.bc -o ${FILE}_obfuscation

echo -e "\n=== Performance Comparison ==="
printf "%-30s %-20s %-20s\n" "Metric" "No Obfuscation" "With Obfuscation"
echo "--------------------------------------------------------------------------"
# Measure time
# NO_OBF_TIME=$( (/usr/bin/time -f "%e" ./${FILE}_no_obfuscation > /dev/null) 2>&1 )
OBF_TIME=$( (/usr/bin/time -f "%e" ./${FILE}_obfuscation > /dev/null) 2>&1 )


#printf "%-30s %-20s %-20s\n" "Execution Time (s)" "$NO_OBF_TIME" "$OBF_TIME"
printf "%-30s %-20s %-20s\n" "Execution Time (s)" "$OBF_TIME"

# Binary size
NO_OBF_SIZE=$(stat --format=%s ${FILE}_no_obfuscation)
OBF_SIZE=$(stat --format=%s ${FILE}_obfuscation)
printf "%-30s %-20s %-20s\n" "Binary Size (bytes)" "$NO_OBF_SIZE" "$OBF_SIZE"
# perf stats
perf stat -e cycles,instructions,cache-misses,branches,branch-misses -x, -o perf_no_obf.txt ./${FILE}_no_obfuscation
perf stat -e cycles,instructions,cache-misses,branches,branch-misses -x, -o perf_obf.txt ./${FILE}_obfuscation
# Extract and print metrics
for METRIC in cycles instructions cache-misses branches branch-misses
do
    NO_VAL=$(grep "$METRIC" perf_no_obf.txt | cut -d',' -f1 | sed 's/ //g')
    OBF_VAL=$(grep "$METRIC" perf_obf.txt | cut -d',' -f1 | sed 's/ //g')
    printf "%-30s %-20s %-20s\n" "$METRIC" "$NO_VAL" "$OBF_VAL"
done

# Cleanup perf files if needed
# rm -f perf_no_obf.txt perf_obf.txt
