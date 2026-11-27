#!/usr/bin/env bash
# S0 structural scan on a built Lean project (generalised copy; the original is for Candle).
# usage: run.sh PROJECT_DIR OUT_DIR MAP_TSV [MANIFEST]
#   PROJECT_DIR  Lean project with a built .lake (lake env lean must work there)
#   OUT_DIR      writes report.json, summary.txt, lean_dump.txt
#   MAP_TSV      map file for this run
#   MANIFEST     optional TSV "lean theorem name<TAB>sha256 of statement text"
# env: S0_ROOT   root module/namespace of the project (default CmlTS); S0_HOL4 statements.jsonl; PYTHON
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ $# -ge 3 ] || { echo "usage: run.sh PROJECT_DIR OUT_DIR MAP_TSV [MANIFEST]" >&2; exit 2; }
win() { cygpath -m "$1" 2>/dev/null || echo "$1"; }
PROJ="$(cd "$1" && pwd)"
mkdir -p "$2"; OUT="$(cd "$2" && pwd)"
MAP="$(cd "$(dirname "$3")" && pwd)/$(basename "$3")"
MANIFEST="${4:-}"
ROOT="${S0_ROOT:-CmlTS}"
HOL4="${S0_HOL4:-$(win "${STUDY_ROOT:-$HERE/../../..}")/tools/hol4_query/out_ts/statements.jsonl}"
PY="${PYTHON:-python3}"
command -v "$PY" >/dev/null 2>&1 || PY=python

UNF="$(awk -F'\t' '$1=="UNFOLD"{print $3}' "$MAP" | paste -sd, -)"
sed "s/@@ROOT@@/$ROOT/g" "$HERE/DumpLean.lean" > "$OUT/DumpLean_inst.lean"

if [ -z "${S0_SKIP_DUMP:-}" ]; then
echo "[s0] dumping Lean statements from $PROJ (root $ROOT)"
( cd "$PROJ" && S0_UNFOLD="$UNF" lake env lean "$(win "$OUT/DumpLean_inst.lean")" ) > "$OUT/lean_dump.txt" 2> "$OUT/lean_dump.err" || {
  echo "[s0] Lean dump failed, see $OUT/lean_dump.err" >&2; exit 1; }
fi
grep -q '^@@T ' "$OUT/lean_dump.txt" || { echo "[s0] dump has no theorem lines" >&2; exit 1; }

echo "[s0] scanning"
ARGS=(--dump "$(win "$OUT/lean_dump.txt")" --hol4 "$(win "$HOL4")" --map "$(win "$MAP")" --project "$(win "$PROJ")" --out "$(win "$OUT")" --root "$ROOT")
[ -n "$MANIFEST" ] && ARGS+=(--manifest "$(win "$MANIFEST")")
[ -n "${S0_MAKE_MANIFEST:-}" ] && ARGS+=(--make-manifest "$(win "$S0_MAKE_MANIFEST")")
"$PY" -I "$(win "$HERE/scan.py")" "${ARGS[@]}"
echo "[s0] wrote $OUT/report.json and $OUT/summary.txt"
