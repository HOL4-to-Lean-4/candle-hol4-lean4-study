import json, re, collections
tools = collections.Counter(); flags = set()
BS = chr(92)
for l in open('E:/ts_ws/prove/run_1.jsonl', encoding='utf-8'):
    o = json.loads(l)
    if o['type'] != 'assistant':
        continue
    for c in o['message']['content']:
        if c.get('type') != 'tool_use':
            continue
        tools[c['name']] += 1
        vals = [v for k, v in c['input'].items() if isinstance(v, str) and not (c['name'] in ('Write', 'Edit') and k != 'file_path')]
        s = ' '.join(vals).replace(BS, '/')
        for q in re.findall(r"([A-Za-z]:/[^\s\"'`]+|(?<![\w.])/[a-z]/[^\s\"'`]+|~/[^\s\"'`]+|\.\./[^\s\"'`]+)", s):
            n = q.lower()
            if not n.startswith(('e:/ts_ws/prove/ws', '/e/ts_ws/prove/ws')) and '.elan/toolchains' not in n:
                flags.add((c['name'], q[:140]))
        if c['name'] in ('Write', 'Edit'):
            body = ' '.join(str(v) for v in c['input'].values())
            if re.search(r'IO\.FS|IO\.Process|readFile|System\.FilePath', body):
                flags.add(('IO?', c['input'].get('file_path', '')[-60:]))
print(tools)
for f in sorted(flags):
    print(f)
