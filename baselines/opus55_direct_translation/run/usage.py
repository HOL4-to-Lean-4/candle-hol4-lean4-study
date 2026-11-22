import json,sys
for name in ['stage1','A','B','C','D']:
    seen={};ts=[];last=None;tools=0;models=set()
    for l in open(f'transcripts/{name}.jsonl'):
        try:o=json.loads(l)
        except: continue
        if o.get('timestamp'): ts.append(o['timestamp'])
        m=o.get('message')
        if o.get('type')=='assistant' and isinstance(m,dict):
            if m.get('model'): models.add(m['model'])
            for c in m.get('content') or []:
                if isinstance(c,dict) and c.get('type')=='tool_use': tools+=1
                if isinstance(c,dict) and c.get('type')=='text': last=c['text']
            if m.get('usage'): seen[m.get('id')]=m['usage']
    tot={k:sum((u.get(k) or 0) for u in seen.values()) for k in ['input_tokens','output_tokens','cache_read_input_tokens','cache_creation_input_tokens']}
    print(name,min(ts),max(ts),len(seen),tools,models,tot)
    if len(sys.argv)>1 and name in sys.argv[1:]: print(last)
