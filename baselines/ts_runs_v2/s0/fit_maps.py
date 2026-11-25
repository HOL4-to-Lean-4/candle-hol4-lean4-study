#!/usr/bin/env python3
"""Apply the post-hoc (fitted) edits to the frozen v0 maps: map_<run>.v0.tsv -> map_<run>.tsv.
Every edit is made AFTER looking at a disagreement of the v0 scan and gets status `fitted`.
ops: ('set', kind, hol, lean, perm, note)  replace the row with this kind and hol (first match; lean-key for rows without hol)
     ('add', kind, hol, lean, perm, note)  append a row
     ('append', kind, hol, lean_extra, note) add Lean names to the lean field of an existing row
usage: fit_maps.py   (writes the three final maps)
"""
import sys

RUNS = ['opus_lessons', 'opus_nolessons', 'sonnet_lessons']
common = [
    ('set', 'TYPE', 'namespace$namespace', 'Namespace', '', 'slip in v0: CONVENTIONS rename namespace -> Namespace was missing from the builder'),
]
edits = {r: [('set', 'TYPE', 'namespace$namespace', ('CmlTS.' if r.startswith('opus') else '') + 'Namespace', '', common[0][5])] for r in RUNS}
edits['sonnet_lessons'] += [
    ('add', 'CONST', 'weakening$weakS', 'weakS_poly', '', 'weakS_poly is the polymorphic version of weakS (not in CONVENTIONS, found in Weakening.lean)'),
    ('add', 'CONST', 'weakening$weakCT', 'weakCT_poly', '', 'weakCT_poly is the polymorphic version of weakCT (not in CONVENTIONS, found in Weakening.lean)'),
]
exec(open('E:/ts_ws/s0/fit_edits_extra.py', encoding='utf-8').read()) if __import__('os').path.exists('E:/ts_ws/s0/fit_edits_extra.py') else None


def apply(run):
    lines = open('E:/ts_ws/s0/map_%s.v0.tsv' % run, encoding='utf-8').read().split(chr(10))
    out = []
    pending = list(edits[run])
    adds = []
    for e in pending:
        if e[0] == 'add':
            adds.append(e)
    for ln in lines:
        if not ln.strip() or ln.startswith('#') or ln.startswith('kind' + chr(9)):
            out.append(ln)
            continue
        f = ln.split(chr(9))
        f += [''] * (6 - len(f))
        done = False
        for e in pending:
            if e[0] == 'set' and f[0] == e[1] and f[1] == e[2]:
                f = [e[1], e[2], e[3], e[4], 'fitted', e[5]]
                done = True
            elif e[0] == 'append' and f[0] == e[1] and f[1] == e[2]:
                f[2] = f[2] + ',' + e[3]
                f[4] = 'fitted'
                f[5] = f[5] + ' | fitted: ' + e[4]
                done = True
        out.append(chr(9).join(f))
    for e in adds:
        out.append(chr(9).join([e[1], e[2], e[3], e[4], 'fitted', e[5]]))
    open('E:/ts_ws/s0/map_%s.tsv' % run, 'w', encoding='utf-8', newline=chr(10)).write(chr(10).join(out).rstrip(chr(10)) + chr(10))


for r in RUNS:
    apply(r)
print('ok')
