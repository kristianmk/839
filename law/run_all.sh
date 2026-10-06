#!/bin/bash
# The pipeline that produced the published laws: build the kernel, then for the periods
# 16, 32, 64, 128 and 256 search (each period starts from the law of the previous one) and
# certify; at the end verify every certified law again with independent code.
#
# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
#
# usage: PYTHON=python3 THREADS=9 ./run_all.sh        (several hours for period 256)
set -euo pipefail
cd "$(dirname "$0")"
PYTHON=${PYTHON:-python3}
THREADS=${THREADS:-9}

cmake -S . -B build -DCMAKE_BUILD_TYPE=Release > build.log 2>&1
cmake --build build >> build.log 2>&1

previous=-
for spec in 16:300 32:600 64:1500 128:2500 256:3500; do
    N=${spec%%:*}; rounds=${spec##*:}
    "$PYTHON" law_cg.py "$N" "$rounds" "law$N.json" 0 "$previous" "$THREADS" > "law$N.log" 2>&1
    "$PYTHON" law_certify.py "law$N.json" "law${N}_certified.json" > "certify$N.log" 2>&1
    previous="law$N.json"
done
for N in 16 32 64 128 256; do
    "$PYTHON" law_check_iv.py "law${N}_certified.json" > "check$N.log" 2>&1
done
echo "all periods searched, certified and checked" > run_all.done
