#!/usr/bin/env bash

set -euo pipefail

# Always fetch Mathlib (and other) oleans from cache — never compile Mathlib from scratch.
lake exe cache get

lake exe vbp build

# Post-build UX: stable statement permalinks + drill-down TOC.
python3 scripts/enhance-site-ux.py

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
test -f _out/site/html-multi/site-ux.css
test -f _out/site/html-multi/site-ux.js
