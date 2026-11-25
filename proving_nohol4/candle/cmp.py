import re,io,glob,os,difflib
# every base line must still be present in order, except proofs replaced: compare declarations' headers
def hdrs(d):
    out={}
    for f in glob.glob(d+'/**/*.lean',recursive=True):
        t=io.open(f,encoding='utf-8').read()
        for m in re.finditer(r'^(?:@\[[^\]]*\]\s*)?theorem\s+([^\s({\[:]+)(.*?):=\s*(?:by\b|fun|by\s)',t,re.M|re.S):
            out[(os.path.basename(f),m.group(1))]=re.sub(r'\s+',' ',m.group(2))
    return out
a=hdrs('E:/ts_ws/prove2_ctl/candle/base_copy'); b=hdrs('E:/prove2/candle/ws/lean/CandleLean')
print(len(a),'missing',[k for k in a if k not in b][:5],'changed',[k for k in a if k in b and a[k]!=b[k]])
# line-level: lines removed from base that are not sorry/import
tot=0
for f in glob.glob('E:/ts_ws/prove2_ctl/candle/base_copy/**/*.lean',recursive=True):
    r=os.path.relpath(f,'E:/ts_ws/prove2_ctl/candle/base_copy')
    x=io.open(f,encoding='utf-8').read().split('\n'); y=io.open('E:/prove2/candle/ws/lean/CandleLean/'+r,encoding='utf-8').read().split('\n')
    for l in difflib.unified_diff(x,y,n=0,lineterm=''):
        if l.startswith('-') and not l.startswith('---'):
            tot+=1
            if 'sorry' not in l: print(r,l[:150])
print('removed lines',tot)
