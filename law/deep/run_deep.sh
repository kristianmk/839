#!/bin/bash
# The second stage of the search for the law of period 256: build law_deep, continue from the
# law of the first stage (../law256.json), certify the result and verify it again with
# independent code.
#
# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
#
# usage: PYTHON=python3 THREADS=9 ./run_deep.sh        (about two hours)
set -euo pipefail
cd "$(dirname "$0")"
PYTHON=${PYTHON:-python3}
THREADS=${THREADS:-9}

cmake -S . -B build -DCMAKE_BUILD_TYPE=Release > build.log 2>&1
cmake --build build >> build.log 2>&1

"$PYTHON" law_deep.py ../law256.json 700 law256_deep.json "$THREADS" 20 4 1e-4 1 > law256_deep.log 2>&1
"$PYTHON" ../law_certify.py law256_deep.json law256_deep_certified.json > certify256_deep.log 2>&1
"$PYTHON" ../law_check_iv.py law256_deep_certified.json > check256_deep.log 2>&1
echo "second stage searched, certified and checked" > run_deep.done
