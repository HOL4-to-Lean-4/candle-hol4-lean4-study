#!/bin/bash
# Run one Gemini Neon review.  Usage: neon_review.sh REQUEST_DIR
# REQUEST_DIR holds prompt.md plus any files to review. Neon runs with REQUEST_DIR as
# its working directory (it can read the files; print mode denies tools that need
# approval). Writes REQUEST_DIR/response.md and REQUEST_DIR/response.json
# (model, conversation id, token usage). Exit 2 = agy needs a new sign-in.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
dir=$(cd "$1" && pwd)
model=${NEON_MODEL:-gemini-4-neon-high}
bash "$here/neon_check.sh" >/dev/null; rc=$?; [ $rc -ne 0 ] && { echo "agy not signed in (rc=$rc)"; exit $rc; }
eval "$(bash "$here/start_keyring.sh")"; export PATH=$HOME/.local/bin:$PATH
cd "$dir"
agy --model "$model" --output-format json --print-timeout "${NEON_TIMEOUT:-3600s}" \
    -p "$(cat prompt.md)" > response.raw.json 2> response.stderr
python3 - "$model" <<'PY'
import json,sys,datetime
r=json.load(open('response.raw.json'))
open('response.md','w').write(r.get('response',''))
meta={k:r.get(k) for k in ('conversation_id','status','duration_seconds','num_turns','usage')}
meta['model_requested']=sys.argv[1]; meta['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
json.dump(meta,open('response.json','w'),indent=1); print(meta['status'],meta['usage'])
PY
