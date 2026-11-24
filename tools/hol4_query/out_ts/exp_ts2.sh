B=~/candle_build/repo/_build
export PATH=$B/polyml/bin:$B/HOL/bin:/usr/bin:/bin LD_LIBRARY_PATH=$B/polyml/lib HOLDIR=$B/HOL
S=/mnt/c/Users/my-pc/AppData/Local/Temp/claude/d8c797a174aa3946/48c45501-b365-43b5-98a7-2f8320085a63/scratchpad
rm -rf ~/ts_export && mkdir ~/ts_export && cp ~/ts_build/hol4-ultramin/*.sml ~/ts_build/hol4-ultramin/Holmakefile ~/ts_export/
cd ~/ts_export
python3 - <<'PY'
import re,glob
for f in glob.glob('*Script.sml'):
    s=open(f,encoding='utf-8',errors='surrogateescape').read()
    th=f[:-10]
    def r(m):
        n=m.group(2)
        if (th,n) in(('typeSound','EVERY_LIST_REL'),('typeSysProps','tveLookup_freevars')): n=n+'_local'
        a=[x for x in m.group(3).split(',') if x.strip()!='local']
        return m.group(1)+n+('['+','.join(a)+']' if a else '')
    s2=re.sub(r"^(Theorem |Triviality )([\w']+)\[([^\]]*\blocal\b[^\]]*)\]",r,s,flags=re.M)
    s2=re.sub(r"^val type_v_exn = SIMP_RULE",'val type_v_exn = save_thm("type_v_exn", SIMP_RULE',s2,flags=re.M)
    if s2!=s: open(f,'w',encoding='utf-8',errors='surrogateescape').write(s2)
PY
sed -n 393,403p typeSoundScript.sml
