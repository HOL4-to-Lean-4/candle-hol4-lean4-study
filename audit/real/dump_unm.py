import score as s
for st in ["S3a","S3b","S1"]:
    for k,f,v in s.unm[st]:
        print("##",st,k["unit"],k["kind"],k["translation"],k["module"],f["id"],f["class"],f["declaration"],"| review:",v)
        print("   ",str({a:b for a,b in f.items() if a not in("id","class","declaration")})[:420])
