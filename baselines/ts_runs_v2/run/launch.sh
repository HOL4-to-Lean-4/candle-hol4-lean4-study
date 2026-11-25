#!/bin/bash
# usage: launch.sh <dir-of-workspace> <model> <settings> <prompt-file> <out-prefix>
export CLAUDE_CODE_GIT_BASH_PATH='D:\Git\bin\bash.exe'
cd "$1" || exit 1
date -u +%FT%TZ > "$5.start"
env -u CLAUDECODE claude -p "$(cat "$4")" --model "$2" --effort high --settings "$3" --setting-sources "" --strict-mcp-config --disable-slash-commands --tools "Read,Write,Edit,Glob,Grep,Bash" --permission-mode dontAsk --output-format stream-json --verbose < /dev/null > "$5.jsonl" 2> "$5.err"
echo "rc=$?" > "$5.done"; date -u +%FT%TZ >> "$5.done"
