import io,sys
ren={'true':'true_','false':'false_','instance':'instance_'}
pk=set("misc mllist mlstring location lprefix_lub ffi fpSem namespace namespaceProps ast semanticPrimitives semanticPrimitivesProps evaluate evaluateProps semantics_min typeSystem typeSoundInvariants weakening typeSysProps typeSound".split())
for r in ['opus_lessons','opus_nolessons','sonnet_lessons']:
    L={}
    for l in io.open('leantv_%s.tsv'%r,encoding='utf-8'):
        c=l.rstrip('\n').split('\t')
        if c[0]=='L': L.setdefault(c[2].split('.')[-1],[]).append(c)
    n=m=0
    print('==',r)
    for l in io.open('consts_ts.tsv',encoding='utf-8'):
        c=l.rstrip('\n').split('\t')
        if c[0]!='CONST' or c[1] not in pk: continue
        nm=ren.get(c[2],c[2])
        if nm in L:
            n+=1
            ks={int(x[3]) for x in L[nm]}
            if int(c[3]) not in ks: m+=1; print('  ',c[1],nm,'HOL',c[3],c[4][:110],'| LEAN',sorted(ks),L[nm][0][4][:110].encode('ascii','replace').decode())
    print(n,'compared',m,'differ')
