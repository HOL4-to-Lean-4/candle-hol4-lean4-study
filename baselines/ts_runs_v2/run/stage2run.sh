#!/bin/bash
W="${WORK_ROOT:-/e}"; W="${W%/}"   # folder holding ts_ws/ and prove2/ (default: E: drive in Git Bash)
R=$W/ts_ws/runs
one() { r=$1; m=$2; a=$3; $W/ts_ws/common/launch.sh $R/$r/ws2$a $m "$(cygpath -m $R/$r/settings.json 2>/dev/null || echo $R/$r/settings.json)" $R/$r/stage2_brief.md $R/$r/stage2$a; }
export -f one; export R W
{ for x in "opus_lessons_v2 claude-opus-5-5" "opus_nolessons_v2 claude-opus-5-5" "sonnet_lessons_v2 claude-sonnet-5-5"; do for a in A B C D; do echo "$x $a"; done; done; } | xargs -P 6 -L 1 bash -c 'one $0 $1 $2'
for r in opus_lessons_v2 opus_nolessons_v2 sonnet_lessons_v2; do for a in A B C D; do echo "$r $a $(cat $R/$r/stage2$a.done | tr '\n' ' ')"; done; done
