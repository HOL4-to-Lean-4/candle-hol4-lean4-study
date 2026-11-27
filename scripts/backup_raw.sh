#!/bin/bash
# Pack the raw transcripts and work files that stay out of the public repository and store them in
# the PRIVATE repository HOL4-to-Lean-4/candle-hol4-lean4-raw (needs gh, signed in, and git push access):
# committed as plain files under raw-<date>/ (so a cloud session gets them with git clone), and also
# uploaded to the release raw-<date>.  Git Bash:  bash scripts/backup_raw.sh
# Check the files for secrets before running it on new data. Never make that repository public.
# Archives are dated and complete; to restore, only the newest one is needed (see CONTINUE.md).
set -e -o pipefail
N=candle_raw_$(date +%F); R=HOL4-to-Lean-4/candle-hol4-lean4-raw; T=raw-$(date +%F)
[ "$(gh api repos/$R --jq .private)" = true ] || { echo "$R is not private; nothing uploaded"; exit 1; }
cd /e
{
  for d in ts_ws/runs ts_ws/runs_run0_incomplete_src ts_ws/prove ts_ws/prove_ts ts_ws/prove2_ctl ts_ws/probe ts_ws/ground prove2; do
    if [ -d "$d" ]; then find "$d" -type f -not -path "*/.lake/*" -not -path "*/HOL4-src/*" -not -path "*/hol4/*" -not -path "*/__pycache__/*"; fi
  done
  find ts_ws/mut_work -maxdepth 1 -type f
  find NUS/mcomp/Dissertation/candle_study/audit -path "*runs*" \( -name "*.raw" -o -name "*.err" -o -name "*.last" \)
  # the withheld scoring keys, so that cloud sessions can run analyse.py and make_csv.py
  for f in NUS/mcomp/Dissertation/candle_study/baselines/ts_runs_v2/scoring/key.csv NUS/mcomp/Dissertation/candle_study/audit/real/check/check_key.csv; do
    [ -f "$f" ] && echo "$f"
  done
} | sort -u > ts_ws/$N.files.txt
if xargs -d '\n' grep -lIE "sk-(ant|proj)-[A-Za-z0-9_-]{10}|gh[po]_[A-Za-z0-9]{20}|AIza[0-9A-Za-z_-]{30}|ya29\.|\"(refresh|access)_token\"" < ts_ws/$N.files.txt; then
  echo "possible secrets in the files above; nothing uploaded"; exit 1
fi
tar -czf ts_ws/$N.tar.gz -T ts_ws/$N.files.txt
cd ts_ws
sha256sum $N.tar.gz > $N.tar.gz.sha256
gh release view $T -R $R >/dev/null 2>&1 || gh release create $T -R $R --title "Raw files, ${T#raw-}" --notes "Private: holds account details."
gh release upload $T $N.tar.gz $N.tar.gz.sha256 $N.files.txt -R $R --clobber
gh release view $T -R $R --json assets --jq '.assets[]|[.name,.size]|@tsv'
# Commit the same files into the repository (GitHub refuses files over 100 MB; keep the release then).
if [ "$(stat -c %s $N.tar.gz)" -lt 95000000 ]; then
  C=$(mktemp -d); git clone -q --depth 1 https://github.com/$R.git "$C"
  mkdir -p "$C/$T"; cp $N.tar.gz $N.tar.gz.sha256 $N.files.txt "$C/$T/"
  git -C "$C" add "$T" && git -C "$C" commit -q -m "Raw files, ${T#raw-}" && git -C "$C" push -q origin HEAD:main
  rm -rf "$C"
else
  echo "$N.tar.gz is over 95 MB: kept in the release only"
fi
