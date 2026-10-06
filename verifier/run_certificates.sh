#!/bin/sh
# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
#
# Runs the verifier on the three certificates of the paper and writes its result line into each
# certificate folder (cpp_verification.json). Needs build/verify and build/verify8 (see
# CMakeLists.txt).
#   usage: ./run_certificates.sh [DIR]     DIR holds the certificate folders (default: ..)
set -eu
here=$(cd "$(dirname "$0")" && pwd)
dir=${1:-"$here/.."}
parameters=$(mktemp)
trap 'rm -f "$parameters"' EXIT
for name in certificate certificate_line certificate_third; do
    python3 "$here/make_parameters.py" "$dir/$name/inputs.json" "$parameters"
    # frames of eight points (the entry "points" of inputs.json) need the program built for eight
    points=$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1])).get("points", 7))' "$dir/$name/inputs.json")
    case "$points" in
        7) program="$here/build/verify" ;;
        8) program="$here/build/verify8" ;;
        *) echo "$name: no verifier is built for frames of $points points" >&2; exit 1 ;;
    esac
    "$program" "$parameters" "$dir/$name/kernel_lower.bin" > "$dir/$name/cpp_verification.json"
    echo "$name: $(cat "$dir/$name/cpp_verification.json")"
done
