import json,re,sys
allowed={'stage1':'/home/claude/work/ws/','A':'/home/claude/work/wsA/','B':'/home/claude/work/wsB/','C':'/home/claude/work/wsC/','D':'/home/claude/work/wsD/'}
for k,ws in allowed.items():
    tools={};flag=[]
    for l in open(f'transcripts/{k}.jsonl'):
        o=json.loads(l);m=o.get('message')
        if o.get('type')!='assistant' or not isinstance(m,dict): continue
        for c in m.get('content') or []:
            if not(isinstance(c,dict) and c.get('type')=='tool_use'): continue
            n=c['name'];tools[n]=tools.get(n,0)+1
            s=json.dumps(c['input'])
            for p in re.findall(r'(/(?:home|mnt|tmp|root|etc|usr|opt)[^\s"\'\;|&)]*)',s):
                if p.startswith(ws) or '.elan/toolchains' in p or p.startswith('/home/claude/.elan') or p in('/tmp','/dev/null'): continue
                flag.append((n,p))
            if re.search(r'\b(git|curl|wget)\b',s) and n=='Bash': flag.append((n,'net/git? '+s[:150]))
    print(k,tools); 
    for f in sorted(set(flag)): print('   ',f)
