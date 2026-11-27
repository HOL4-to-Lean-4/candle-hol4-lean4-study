# Paths: set STUDY_ROOT (this repository), WORK_ROOT (folder holding ts_ws/, auditreal/, ...)
# and DISS_ROOT to override. Defaults: the repo root; E:/ on Windows, ~/work/ elsewhere; parent of the repo.
import os as _os
def _repo_root():
    d = _os.path.dirname(_os.path.abspath(__file__))
    while not _os.path.exists(_os.path.join(d, "CLOUD.md")) and _os.path.dirname(d) != d:
        d = _os.path.dirname(d)
    return d
_STUDY = _os.environ.get("STUDY_ROOT", _repo_root()).replace("\\", "/").rstrip("/")
_WR = _os.environ.get("WORK_ROOT", "E:/" if _os.name == "nt" else _os.path.expanduser("~/work")).replace("\\", "/").rstrip("/") + "/"
_DISS = _os.environ.get("DISS_ROOT", _os.path.dirname(_STUDY)).replace("\\", "/").rstrip("/") + "/"
import re,io,glob,os,difflib
# every base line must still be present in order, except proofs replaced: compare declarations' headers
def hdrs(d):
    out={}
    for f in glob.glob(d+'/**/*.lean',recursive=True):
        t=io.open(f,encoding='utf-8').read()
        for m in re.finditer(r'^(?:@\[[^\]]*\]\s*)?theorem\s+([^\s({\[:]+)(.*?):=\s*(?:by\b|fun|by\s)',t,re.M|re.S):
            out[(os.path.basename(f),m.group(1))]=re.sub(r'\s+',' ',m.group(2))
    return out
a=hdrs(_WR + 'ts_ws/prove2_ctl/candle/base_copy'); b=hdrs(_WR + 'prove2/candle/ws/lean/CandleLean')
print(len(a),'missing',[k for k in a if k not in b][:5],'changed',[k for k in a if k in b and a[k]!=b[k]])
# line-level: lines removed from base that are not sorry/import
tot=0
for f in glob.glob(_WR + 'ts_ws/prove2_ctl/candle/base_copy/**/*.lean',recursive=True):
    r=os.path.relpath(f,_WR + 'ts_ws/prove2_ctl/candle/base_copy')
    x=io.open(f,encoding='utf-8').read().split('\n'); y=io.open(_WR + 'prove2/candle/ws/lean/CandleLean/'+r,encoding='utf-8').read().split('\n')
    for l in difflib.unified_diff(x,y,n=0,lineterm=''):
        if l.startswith('-') and not l.startswith('---'):
            tot+=1
            if 'sorry' not in l: print(r,l[:150])
print('removed lines',tot)
