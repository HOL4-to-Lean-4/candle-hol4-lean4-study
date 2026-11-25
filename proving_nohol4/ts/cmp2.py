import io,glob,os,difflib,re
B="E:/ts_ws/prove2_ctl/ts/base_copy"; W="E:/prove2/ts/ws/lean/CmlTS"
tot=sor=other=0; bad=[]
for f in glob.glob(B+"/**/*.lean",recursive=True):
    r=os.path.relpath(f,B)
    x=io.open(f,encoding="utf-8").read().split("\n"); y=io.open(W+"/"+r,encoding="utf-8").read().split("\n")
    ys=set(l.strip() for l in y)
    for l in difflib.unified_diff(x,y,n=0,lineterm=""):
        if l.startswith("-") and not l.startswith("---"):
            tot+=1
            if "sorry" in l: 
                sor+=1
                h=l[1:].split(":=")[0].strip()
                if h and h!="sorry" and not any(q.startswith(h) for q in ys): bad.append((r,l))
            else:
                other+=1
                h=l[1:].strip()
                if not (h.endswith(":= by") and any(q.startswith(h[:-2].strip()) for q in ys)): bad.append((r,l))
print(tot,sor,other,bad)
r=lambda p:{l.split("\t")[1]:l for l in open(p,encoding="utf-8").read().split("\n") if l}
a,b=r("E:/ts_ws/prove2_ctl/ts/frozen_base.tsv"),r("E:/ts_ws/prove2_ctl/ts/frozen_end.tsv")
m=[n for n in a if n not in b]; print("missing",len(m),[n for n in m if "match_" not in n and "splitter" not in n]); print("changed",[(a[n],b[n]) for n in a if n in b and a[n]!=b[n]])
print("new axioms/opaques",[b[n] for n in b if n not in a and b[n].startswith(("axiom","opaque"))])
