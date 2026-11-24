#!/usr/bin/env bash
# S0 structural scan on a built Lean project.
# usage: run.sh PROJECT_DIR [OUT_DIR] [MANIFEST]
#   PROJECT_DIR  Lean project with a built .lake (lake env lean must work there)
#   OUT_DIR      default: ./out next to this script; writes report.json, summary.txt, lean_dump.txt
#   MANIFEST     optional TSV "lean theorem name<TAB>sha256 of statement text" (scan.py --make-manifest writes one)
# env: S0_HOL4 = path of statements.jsonl (default ../hol4_query/out/statements.jsonl), PYTHON = python executable
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ $# -ge 1 ] || { echo "usage: run.sh PROJECT_DIR [OUT_DIR] [MANIFEST]" >&2; exit 2; }
win() { cygpath -m "$1" 2>/dev/null || echo "$1"; }
PROJ="$(cd "$1" && pwd)"
OUT="${2:-$HERE/out}"
mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"
MANIFEST="${3:-}"
HOL4="${S0_HOL4:-$HERE/../hol4_query/out/statements.jsonl}"
PY="${PYTHON:-python3}"
command -v "$PY" >/dev/null 2>&1 || PY=python

# Lean definitions that map.tsv declares as abbreviations (UNFOLD rows) must have their values dumped.
UNF="$(awk -F'\t' '$1=="UNFOLD"{print $3}' "$HERE/map.tsv" | paste -sd, -)"

echo "[s0] dumping Lean statements from $PROJ"
( cd "$PROJ" && S0_UNFOLD="$UNF" lake env lean "$(win "$HERE/DumpLean.lean")" ) > "$OUT/lean_dump.txt" 2> "$OUT/lean_dump.err" || {
  echo "[s0] Lean dump failed, see $OUT/lean_dump.err" >&2; exit 1; }
grep -q '^@@T ' "$OUT/lean_dump.txt" || { echo "[s0] dump has no theorem lines" >&2; exit 1; }

echo "[s0] scanning"
ARGS=(--dump "$(win "$OUT/lean_dump.txt")" --hol4 "$(win "$HOL4")" --map "$(win "$HERE/map.tsv")" --project "$(win "$PROJ")" --out "$(win "$OUT")")
[ -n "$MANIFEST" ] && ARGS+=(--manifest "$(win "$MANIFEST")")
[ -n "${S0_MAKE_MANIFEST:-}" ] && ARGS+=(--make-manifest "$(win "$S0_MAKE_MANIFEST")")
"$PY" -I "$(win "$HERE/scan.py")" "${ARGS[@]}"
echo "[s0] wrote $OUT/report.json and $OUT/summary.txt"
