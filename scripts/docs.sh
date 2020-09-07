#!/usr/bin/env bash
set -euo pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# run in repo root
cd "$DIR/.."

ALECTRYON="${1-alectryon.py}"
ALECTRYON_FLAGS="-R src POCS --output-directory doc"

mkdir -p doc

for file in src/*.v; do
    if [ ! -f "$file" ]; then
        continue
    fi
    echo $file
    filename=$(basename $file)
    ${ALECTRYON} ${ALECTRYON_FLAGS} --frontend coqdoc $file --output "doc/${filename}.html" &
done
wait

for dir in src/*; do
    dirname=$(basename $dir)
    for file in $dir/*.v; do
        if [ ! -f "$file" ]; then
            continue
        fi
        echo $file
        filename=$(basename $file)
        ${ALECTRYON} ${ALECTRYON_FLAGS} --frontend coqdoc $file --output "doc/${dirname}.${filename}.html" &
    done
    wait
done
