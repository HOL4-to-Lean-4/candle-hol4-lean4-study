B=~/candle_build/repo/_build
export PATH=$B/polyml/bin:$B/HOL/bin:/usr/bin:/bin LD_LIBRARY_PATH=$B/polyml/lib HOLDIR=$B/HOL
S=/mnt/c/Users/my-pc/AppData/Local/Temp/claude/d8c797a174aa3946/48c45501-b365-43b5-98a7-2f8320085a63/scratchpad
cd ~/ts_export
sed -i '402,403s/metis_tac \[type_v_rules\]));/metis_tac [type_v_rules])));/' typeSoundScript.sml
sed -i '/^Theorem EVERY_LIST_REL_local/,/^QED/{/^QED/a val EVERY_LIST_REL = EVERY_LIST_REL_local;
}' typeSoundScript.sml; grep -n 'EVERY_LIST_REL_local' typeSoundScript.sml
time Holmake --nolmbc --fast -j 4 2>&1 | tail -15
sed 's/("typeSound","EVERY_LIST_REL")/("typeSound","EVERY_LIST_REL_local"),&/;s/("typeSysProps","tveLookup_freevars")/("typeSysProps","tveLookup_freevars_local"),&/' $S/targets_ts.sml > /tmp/t0.sml
# the target list already holds each duplicated name twice; keep one plain + one _local
python3 - <<'PY'
import re
L=re.findall(r'\("([^"]+)","([^"]+)"\)',open('/mnt/c/Users/my-pc/AppData/Local/Temp/claude/d8c797a174aa3946/48c45501-b365-43b5-98a7-2f8320085a63/scratchpad/targets_ts.sml').read())
seen=set();out=[]
for t in L:
    if t in seen: t=(t[0],t[1]+'_local')
    seen.add(t);out.append(t)
open('/tmp/targets_ts.sml','w').write('val targets = [\n'+',\n'.join('  ("%s","%s")'%t for t in out)+'];\n');print(len(out))
PY
cp $S/export_ts.sml /tmp/
timeout 500 hol run /tmp/export_ts.sml > /tmp/export_ts.raw 2>/tmp/export_ts.err; echo rc=$?; grep -c '^@@JSON' /tmp/export_ts.raw; grep '^@@MISSING' /tmp/export_ts.raw | cut -c1-90
