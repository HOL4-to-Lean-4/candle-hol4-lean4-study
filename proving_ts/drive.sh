#!/bin/bash
# one proving session; resumed after usage-limit stops; 12 h of active time, no spending cap
export CLAUDE_CODE_GIT_BASH_PATH='D:\Git\bin\bash.exe'
P=/e/ts_ws/prove_ts; cd $P/ws || exit 1
SID=$(cat $P/session_id 2>/dev/null); N=$(ls $P/run_*.jsonl 2>/dev/null | wc -l); ACTIVE=$(cat $P/active_s 2>/dev/null || echo 0)
while [ $ACTIVE -lt 43200 ]; do
  N=$((N+1)); T0=$(date +%s); date -u +%FT%TZ >> $P/starts.txt
  if [ -z "$SID" ]; then SID=$(python -c "import uuid;print(uuid.uuid4())"); echo $SID > $P/session_id; ARG="--session-id $SID"; MSG="$(cat $P/BRIEF.md)"; else ARG="--resume $SID"; MSG="Continue the task from where you stopped. The brief still applies. If everything provable is done, build the project and give the final report."; fi
  env -u CLAUDECODE claude -p "$MSG" $ARG --model claude-opus-5-5 --effort high --settings $P/settings.json --setting-sources "" --strict-mcp-config --disable-slash-commands --tools "Read,Write,Edit,Glob,Grep,Bash" --permission-mode dontAsk --output-format stream-json --verbose < /dev/null > $P/run_$N.jsonl 2> $P/run_$N.err
  D=$(( $(date +%s) - T0 )); ACTIVE=$((ACTIVE+D)); echo $ACTIVE > $P/active_s; date -u +%FT%TZ >> $P/starts.txt
  if grep -q "RUN COMPLETE" <(tail -5 $P/run_$N.jsonl); then echo complete > $P/status; break; fi
  # usage limit or short failure: wait, then resume (do not count the wait as active time)
  if [ $D -lt 120 ]; then sleep 1800; else sleep 60; fi
done
echo "stopped active=$ACTIVE" >> $P/status
