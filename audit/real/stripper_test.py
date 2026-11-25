import re, sys

BS = chr(92)

def strip_comments(src):
    """Remove block (nested), doc and line comments, aware of string and char literals."""
    out = []
    i, n = 0, len(src)
    ident = re.compile(r"[A-Za-z0-9_'!?À-ɏͰ-Ͽᴀ-ᶿἀ-῿₀-ₜ℀-⅏]")
    chre = re.compile(r"'(\\x[0-9a-fA-F]{2}|\\u\{[0-9a-fA-F]+\}|\\.|[^\\'\n])'")
    while i < n:
        c = src[i]
        if src.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith('/-', j):
                    depth += 1; j += 2
                elif src.startswith('-/', j):
                    depth -= 1; j += 2
                else:
                    j += 1
            out.append('\x00')
            i = j
        elif src.startswith('--', i):
            j = src.find('\n', i)
            if j < 0: j = n
            out.append('\x00')
            i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == BS else 1
            out.append(src[i:j + 1]); i = j + 1
        elif c == "'" and not (i > 0 and ident.match(src[i - 1])):
            m = chre.match(src, i)
            if m:
                out.append(m.group(0)); i = m.end()
            else:
                out.append(c); i += 1
        else:
            out.append(c); i += 1
    text = ''.join(out)
    lines = []
    for ln in text.split('\n'):
        if '\x00' in ln:
            rest = ln.replace('\x00', '')
            if rest.strip() == '':
                continue
            ln = ln.replace('\x00', ' ')
        lines.append(ln.rstrip())
    res = '\n'.join(lines)
    res = re.sub(r"\n{3,}", "\n\n", res)
    return res.strip('\n') + '\n'

if __name__ == '__main__':
    sys.stdout.write(strip_comments(open(sys.argv[1], encoding='utf-8').read()))
