#!/usr/bin/env bash
# Run `codex exec` with Astra through the SSS gateway, with the same flags as audit/real/run.py step S1.
#
#   tools/astra_gateway/codex_astra.sh WORKDIR OUTPREFIX [MODEL] < prompt.md
#
# Writes OUTPREFIX.raw (Codex JSON events), .last (final answer), .err, and .meta.json with:
#   requested model, the model the gateway reports (one tiny probe call just before the run,
#   because Codex events do not carry the model name), Codex token usage, seconds, exit code.
# Needs SSS_BASE_URL and SSS_GPT_KEY (cloud environment "Default") and codex (npm install -g @openai/codex).
# The key stays in the environment; Codex reads it through env_key.
set -euo pipefail
W=$1; OUT=$2; MODEL=${3:-gpt-6.2-astra}
HERE=$(cd "$(dirname "$0")" && pwd)
: "${SSS_BASE_URL:?select cloud environment Default}"; : "${SSS_GPT_KEY:?select cloud environment Default}"
B=${SSS_BASE_URL%/}; [[ $B == */v1 ]] || B=$B/v1
OUT=$(realpath -m "$OUT"); mkdir -p "$(dirname "$OUT")"
export CODEX_HOME=${CODEX_HOME:-$HOME/.codex-sss}; mkdir -p "$CODEX_HOME"

PROBE=$(python3 "$HERE/astra.py" probe -m "$MODEL")

FEATS="memories plugins apps browser_use computer_use multi_agent image_generation skill_search goals in_app_browser tool_suggest"
DIS=(); for f in $FEATS; do DIS+=(--disable "$f"); done

t0=$(date +%s); rc=0
(cd "$W" && codex exec -m "$MODEL" -s read-only --skip-git-repo-check --ephemeral \
  -c model_provider=sss -c model_providers.sss.name=SSS -c "model_providers.sss.base_url=\"$B\"" \
  -c 'model_providers.sss.env_key="SSS_GPT_KEY"' -c 'model_providers.sss.wire_api="responses"' \
  -c project_doc_max_bytes=0 -c web_search=disabled -c model_reasoning_effort=high \
  --json -o "$OUT.last" "${DIS[@]}" -) > "$OUT.raw" 2> "$OUT.err" || rc=$?
dt=$(( $(date +%s) - t0 ))

python3 - "$OUT" "$MODEL" "$dt" "$rc" "$PROBE" <<'EOF'
import json, sys
out, model, dt, rc, probe = sys.argv[1:6]
usage = None
for l in open(out + ".raw", encoding="utf-8", errors="replace"):
    try:
        o = json.loads(l)
    except Exception:
        continue
    if o.get("type") == "turn.completed":
        usage = o.get("usage")
p = json.loads(probe)
meta = {"requested_model": model, "reported_model": p.get("reported_model"), "probe": p, "via": "codex exec + SSS gateway",
        "usage": usage, "seconds": int(dt), "rc": int(rc)}
json.dump(meta, open(out + ".meta.json", "w"), indent=1)
print(json.dumps({k: meta[k] for k in ("requested_model", "reported_model", "usage", "seconds", "rc")}))
EOF
exit $rc
