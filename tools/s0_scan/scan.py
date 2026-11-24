#!/usr/bin/env python3
"""S0: model-free structural scan of Lean theorem statements against the HOL4 kernel export.

No language model, no knowledge of seeded errors. Inputs: the Lean dump (DumpLean.lean output),
statements.jsonl (HOL4 export), map.tsv. For every HOL4 statement the Lean statement of the same name
is translated into the same canonical form as the HOL4 term and compared. See README.md.
"""
import argparse, collections, hashlib, itertools, json, os, re, sys

HOL_CONSTS_ARITY = {'bool$!': 1, 'bool$?': 1, 'bool$/\\': 2, 'bool$\\/': 2, 'bool$~': 1, 'min$==>': 2, 'min$=': 2,
                    'bool$COND': 3}
STD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
BAD_AXIOMS = {'sorryAx', 'Lean.ofReduceBool', 'Lean.trustCompiler'}

# ------------------------------------------------------------------ map
class Map:
    def __init__(self, path):
        self.hol2lean, self.lean2hol, self.status = {}, {}, collections.Counter()
        self.type_h2l, self.type_l2h = {}, {}
        self.unfold, self.allow_opaque, self.rows = set(), set(), []
        for ln in open(path, encoding='utf-8'):
            if ln.startswith('#') or not ln.strip() or ln.startswith('kind\t'):
                continue
            f = ln.rstrip('\n').split('\t')
            f += [''] * (6 - len(f))
            kind, hol, lean, perm, status, note = f[:6]
            self.rows.append(f[:6])
            self.status[status] += 1
            names = [x for x in lean.split(',') if x]
            if kind == 'CONST':
                pm = [int(x) for x in perm.split(',')] if perm else None
                self.hol2lean[hol] = (names, pm)
                for n in names:
                    self.lean2hol[n] = (hol, pm)
            elif kind == 'TYPE':
                self.type_h2l[hol] = names
                for n in names:
                    self.type_l2h[n] = hol
            elif kind == 'UNFOLD':
                self.unfold.update(names)
            elif kind == 'ALLOW':
                self.allow_opaque.update(names)
            elif kind == 'NAME':
                pass

# ------------------------------------------------------------------ canonical terms (tuples)
# ('v',id) ('c',name) ('ap',head,args) ('lam',id,ty,body) ('all',id,ty,body) ('ex',id,ty,body)
# ('imp',prems,concl) ('and',items) ('or',items) ('not',a) ('eq',a,b) ('ite',c,a,b) ('case',discrs,alts)
# ('num',n) ('str',s) ('chr',n) ('true',) ('false',) ('unk',txt)   types: ('ty',name,args) ('tv',id) ('fun',a,b)
TRUE, FALSE = ('true',), ('false',)
_fresh = itertools.count(1)
TANY = ('ty', '?', ())


def fresh():
    return 'u%d' % next(_fresh)


def AND(items):
    out = []
    for x in items:
        out.extend(x[1] if x[0] == 'and' else [x])
    return out[0] if len(out) == 1 else ('and', tuple(out))


def OR(items):
    out = []
    for x in items:
        out.extend(x[1] if x[0] == 'or' else [x])
    return out[0] if len(out) == 1 else ('or', tuple(out))


def IMP(prems, concl):
    ps = []
    for p in prems:
        ps.extend(p[1] if p[0] == 'and' else [p])
    if concl[0] == 'imp':
        ps.extend(concl[1])
        concl = concl[2]
    return ('imp', tuple(ps), concl) if ps else concl


def AP(h, args):
    args = tuple(args)
    if not args:
        return h
    if h[0] == 'ap':
        return AP(h[1], h[2] + args)
    if h[0] == 'lam':
        return beta(h, args)
    if h[0] == 'c':
        return mk(h[1], list(args), None)
    return ('ap', h, args)


def free_in(t, vid):
    found = [False]

    def f(x):
        if x[0] == 'v' and x[1] == vid:
            found[0] = True
    walk(t, f)
    return found[0]


def LAM(vid, ty, body):
    """lambda with eta reduction: (fun x => f x) is f when x is not free in f."""
    if body[0] == 'ap' and body[2][-1] == ('v', vid):
        head = AP(body[1], body[2][:-1]) if len(body[2]) > 1 else body[1]
        if not free_in(head, vid):
            return head
    return ('lam', vid, ty, body)


def subst(t, vid, val):
    k = t[0]
    if k == 'v':
        return rename_binders(val) if t[1] == vid else t
    if k in ('c', 'num', 'str', 'chr', 'true', 'false', 'unk'):
        return t
    if k == 'ap':
        return AP(subst(t[1], vid, val), [subst(a, vid, val) for a in t[2]])
    if k in ('lam', 'all', 'ex'):
        return (k, t[1], t[2], subst(t[3], vid, val))
    if k == 'imp':
        return ('imp', tuple(subst(a, vid, val) for a in t[1]), subst(t[2], vid, val))
    if k in ('and', 'or'):
        return (k, tuple(subst(a, vid, val) for a in t[1]))
    if k == 'case':
        return ('case', tuple(subst(a, vid, val) for a in t[1]), tuple(subst(a, vid, val) for a in t[2]))
    return (k,) + tuple(subst(a, vid, val) if isinstance(a, tuple) else a for a in t[1:])


def rename_binders(t, m=None):
    m = m or {}
    k = t[0]
    if k == 'v':
        return ('v', m.get(t[1], t[1]))
    if k in ('c', 'num', 'str', 'chr', 'true', 'false', 'unk'):
        return t
    if k == 'ap':
        return ('ap', rename_binders(t[1], m), tuple(rename_binders(a, m) for a in t[2]))
    if k in ('lam', 'all', 'ex'):
        n = fresh()
        m2 = dict(m)
        m2[t[1]] = n
        return (k, n, t[2], rename_binders(t[3], m2))
    if k == 'imp':
        return ('imp', tuple(rename_binders(a, m) for a in t[1]), rename_binders(t[2], m))
    if k in ('and', 'or'):
        return (k, tuple(rename_binders(a, m) for a in t[1]))
    if k == 'case':
        return ('case', tuple(rename_binders(a, m) for a in t[1]), tuple(rename_binders(a, m) for a in t[2]))
    return (k,) + tuple(rename_binders(a, m) if isinstance(a, tuple) else a for a in t[1:])


def beta(f, args):
    args = list(args)
    while args and f[0] == 'lam':
        f = subst(f[3], f[1], args.pop(0))
    return AP(f, args) if args else f


def mk(name, args, st):
    """Build the canonical node for HOL4 constant `name` applied to args (already converted)."""
    n = len(args)
    ar = HOL_CONSTS_ARITY.get(name)
    if name == 'bool$T' and n == 0:
        return TRUE
    if name == 'bool$F' and n == 0:
        return FALSE
    if name in ('bool$!', 'bool$?') and n >= 1 and args[0][0] == 'lam':
        l = args[0]
        node = ('all' if name == 'bool$!' else 'ex', l[1], l[2], l[3])
        return AP(node, args[1:]) if n > 1 else node
    if ar is not None and n >= ar and name not in ('bool$!', 'bool$?'):
        a = args[:ar]
        if name == 'bool$/\\':
            node = AND(a)
        elif name == 'bool$\\/':
            node = OR(a)
        elif name == 'bool$~':
            node = ('not', a[0])
        elif name == 'min$==>':
            node = IMP((a[0],), a[1])
        elif name == 'min$=':
            node = ('eq', a[0], a[1])
        else:
            node = ('ite', a[0], a[1], a[2])
        return AP(node, args[ar:]) if n > ar else node
    if name == 'pair$UNCURRY' and n >= 1:
        f = args[0]
        if n == 1:
            p = fresh()
            return LAM(p, TANY, AP(f, [AP(('c', 'pair$FST'), [('v', p)]), AP(('c', 'pair$SND'), [('v', p)])]))
        p = args[1]
        return AP(AP(f, [AP(('c', 'pair$FST'), [p]), AP(('c', 'pair$SND'), [p])]), args[2:])
    if name == 'num$SUC' and n >= 1:
        return AP(AP(('c', 'arithmetic$+'), [args[0], ('num', 1)]), args[1:])
    if name == 'string$CHR' and n >= 1 and args[0][0] == 'num' and args[0][1] < 256:
        return AP(('chr', args[0][1]), args[1:])
    if name == 'list$CONS' and n == 2 and args[0][0] == 'chr' and args[1][0] == 'str':
        return ('str', chr(args[0][1]) + args[1][1])
    if name == 'bool$IN' and n == 2 and args[1][0] == 'ap' and args[1][1] == ('c', 'list$LIST_TO_SET') and len(args[1][2]) == 1:
        return ('ap', ('c', 'LMEM'), (args[0], args[1][2][0]))
    if name == 'combin$o' and n >= 3:
        return AP(args[0], [AP(args[1], [args[2]])] + list(args[3:]))
    if name == 'option$option_CASE' and n == 3:
        return ('case', (args[0],), (args[1], args[2]))
    if name == 'ternaryComparisons$ordering_CASE' and n == 4:
        return ('case', (args[0],), tuple(args[1:]))
    return ('ap', ('c', name), tuple(args)) if args else ('c', name)


# ------------------------------------------------------------------ HOL4 side
def decode_bits(ty):
    if ty['ty'] == 'one$one':
        return 1
    if ty['ty'] == 'fcp$bit0':
        return 2 * decode_bits(ty['args'][0])
    if ty['ty'] == 'fcp$bit1':
        return 2 * decode_bits(ty['args'][0]) + 1
    raise ValueError('numeric type ' + ty['ty'])


def hty(t):
    if 'tv' in t:
        return ('tv', 'h:' + t['tv'])
    n, a = t['ty'], t['args']
    if n == 'min$fun':
        return ('fun', hty(a[0]), hty(a[1]))
    if n == 'fcp$cart':
        try:
            return ('ty', 'words$word', (('num', decode_bits(a[1])),))
        except Exception:
            pass
    return ('ty', n, tuple(hty(x) for x in a))


def hnum(t):
    """evaluate a HOL4 numeral term below NUMERAL, or None."""
    if 'c' in t:
        return 0 if t['c'] in ('arithmetic$ZERO', 'num$0') else None
    if 'f' in t and 'c' in t['f']:
        c = t['f']['c']
        v = hnum(t['x'])
        if v is None:
            return None
        return 2 * v + 1 if c == 'arithmetic$BIT1' else 2 * v + 2 if c == 'arithmetic$BIT2' else None
    return None


class HolConv:
    def __init__(self):
        self.free = {}
        self.consts = collections.Counter()

    def conv(self, t, env):
        if 'v' in t:
            key = (t['v'], json.dumps(t['t'], sort_keys=True))
            if key in env:
                return ('v', env[key])
            self.free.setdefault(key, ('f:' + t['v'] + ':' + str(len(self.free)), hty(t['t'])))
            return ('v', self.free[key][0])
        if 'c' in t:
            nm = t['c']
            self.consts[nm] += 1
            if nm == 'list$NIL' and t['t']['args'][0] == {'args': [], 'ty': 'string$char'}:
                return ('str', '')
            if nm == 'num$0':
                return ('num', 0)
            return mk(nm, [], self)
        if 'f' in t:
            args = []
            h = t
            while 'f' in h:
                args.append(h['x'])
                h = h['f']
            args.reverse()
            if 'c' in h and h['c'] == 'arithmetic$NUMERAL' and len(args) == 1:
                v = hnum(args[0])
                if v is not None:
                    self.consts['arithmetic$NUMERAL'] += 1
                    return ('num', v)
            cargs = [self.conv(a, env) for a in args]
            if 'c' in h:
                self.consts[h['c']] += 1
                return mk(h['c'], cargs, self)
            return AP(self.conv(h, env), cargs)
        a = t['abs']
        key = (a['v'], json.dumps(a['t'], sort_keys=True))
        nid = fresh()
        e2 = dict(env)
        e2[key] = nid
        return LAM(nid, hty(a['t']), self.conv(t['body'], e2))

    def statement(self, row):
        parts = [self.conv(t, {}) for t in row['hyps']]
        concl = self.conv(row['concl'], {})
        t = IMP(parts, concl) if parts else concl
        # free variables are implicitly universal
        for key, (vid, ty) in sorted(self.free.items(), key=lambda kv: kv[1][0], reverse=True):
            t = ('all', vid, ty, t)
        return t


# ------------------------------------------------------------------ Lean side
class LeanConv:
    def __init__(self, mp, defs):
        self.m, self.defs = mp, defs
        self.unmapped = collections.Counter()
        self.insts = []          # instance binder classes
        self.hol_consts = collections.Counter()  # canonical HOL4 constants reached from Lean
        self.lean_consts = set()  # all Lean constant names mentioned (raw, before unfolding)

    # ---- JSON level unfolding of reducible / UNFOLD definitions
    def unfoldable(self, name):
        d = self.defs.get(name)
        return d is not None and d.get('value') is not None and name not in self.m.lean2hol

    def unfold_json(self, name, xs, ms, cis):
        v = self.defs[name]['value']
        v = self.freshen_json(v)
        xs, ms, cis = list(xs), list(ms), list(cis)
        while v['k'] == 'l' and (xs or ms or cis):
            bi = v['bi']
            if bi in ('i', 's'):
                arg = ms.pop(0) if ms else None
            elif bi == 'c':
                arg = {'k': 'c', 'n': '?inst'} if cis or True else None
                if cis:
                    cis.pop(0)
            else:
                arg = xs.pop(0) if xs else None
            if arg is None:
                break
            v = self.subst_json(v['b'], v['id'], arg)
        return v, xs

    def freshen_json(self, j, m=None):
        m = m if m is not None else {}
        if isinstance(j, list):
            return [self.freshen_json(x, m) for x in j]
        if not isinstance(j, dict):
            return j
        k = j.get('k')
        if k == 'v':
            return {'k': 'v', 'id': m.get(j['id'], j['id'])}
        if k in ('l', 'p'):
            n = 'w%d' % next(_fresh)
            m2 = dict(m)
            m2[j['id']] = n
            out = dict(j)
            out['id'] = n
            out['t'] = self.freshen_json(j['t'], m)
            out['b'] = self.freshen_json(j['b'], m2)
            return out
        return {kk: (self.freshen_json(vv, m) if kk in ('x', 'm', 'h', 'e') else vv) for kk, vv in j.items()}

    def subst_json(self, j, vid, arg):
        if isinstance(j, list):
            return [self.subst_json(x, vid, arg) for x in j]
        if not isinstance(j, dict):
            return j
        k = j.get('k')
        if k == 'v':
            return self.freshen_json(arg) if j['id'] == vid else j
        out = dict(j)
        for kk in ('x', 'm', 'h', 'e', 't', 'b'):
            if kk in out and not isinstance(out[kk], str):
                out[kk] = self.subst_json(out[kk], vid, arg)
        return out

    # ---- types
    def ty(self, j):
        k = j['k']
        if k == 'v':
            return ('tv', j['id'])
        if k == 's':
            return ('ty', 'min$bool', ()) if j['l'] == 'Prop' else ('ty', 'Sort', ())
        if k == 'p':
            return ('fun', self.ty(j['t']), self.ty(j['b']))
        if k in ('c', 'a'):
            name = j['n'] if k == 'c' else j['h']
            xs = [] if k == 'c' else j['x']
            ms = [] if k == 'c' else j['m']
            cis = [] if k == 'c' else j['ci']
            if not isinstance(name, str):
                return ('ty', '?', ())
            self.lean_consts.add(name)
            if name in self.m.type_l2h:
                hn = self.m.type_l2h[name]
                if hn == '@fun':
                    return ('fun', self.ty(xs[0]), self.ty(xs[1]))
                if hn == 'fcp$cart':
                    n = self.term(xs[0]) if xs else TANY
                    return ('ty', 'words$word', (n,))
                return ('ty', hn, tuple(self.ty(x) for x in xs))
            if self.unfoldable(name):
                v, rest = self.unfold_json(name, xs, ms, cis)
                if rest:
                    return ('ty', '?app', ())
                return self.ty(v)
            self.unmapped['type:' + name] += 1
            return ('ty', 'L:' + name, tuple(self.ty(x) for x in xs))
        if k == 'n':
            return ('num', j['v'])
        return ('ty', '?' + k, ())

    # ---- terms
    def term(self, j):
        k = j['k']
        if k == 'v':
            return ('v', j['id'])
        if k == 'n':
            return ('num', j['v'])
        if k == 't':
            return ('rawstr', j['v'])
        if k == 's':
            return ('unk', 'sort')
        if k == 'c':
            return self.app(j['n'], [], [], [])
        if k == 'a':
            if isinstance(j['h'], str):
                return self.app(j['h'], j['x'], j['m'], j['ci'])
            return AP(self.term(j['h']), [self.term(x) for x in j['x']])
        if k == 'l':
            if j['bi'] == 'c':
                return self.term(j['b'])
            if j['dk'] == 'tyvar':
                return self.term(j['b'])
            return LAM(j['id'], self.ty(j['t']), self.term(j['b']))
        if k == 'p':
            if j['bi'] == 'c':
                self.insts.append(self.head_name(j['t']))
                return self.term(j['b'])
            if j['dk'] == 'tyvar':
                return self.term(j['b'])
            if j['dk'] == 'prop':
                return IMP((self.term(j['t']),), self.term(j['b']))
            return ('all', j['id'], self.ty(j['t']), self.term(j['b']))
        if k == 'j':
            if j['s'] == 'Prod' and j['i'] in (0, 1):
                return AP(('c', 'pair$FST' if j['i'] == 0 else 'pair$SND'), [self.term(j['e'])])
            return ('unk', 'proj ' + j['s'])
        return ('unk', k)

    def head_name(self, j):
        if j['k'] == 'a':
            return j['h'] if isinstance(j['h'], str) else '?'
        if j['k'] == 'c':
            return j['n']
        return '?'

    def app(self, name, xs, ms, cis):
        self.lean_consts.add(name)
        if name == 'OfNat.ofNat' and xs and xs[0]['k'] == 'n':
            return ('num', xs[0]['v'])
        if name == 'Char.ofNat' and xs:
            a = self.term(xs[0])
            return ('chrraw', a[1]) if a[0] == 'num' else ('unk', 'Char.ofNat')
        if name == 'HOL.ch' and xs:
            a = self.term(xs[0])
            return ('chr', a[1] % 256) if a[0] == 'chrraw' else AP(('c', 'HOL.ch'), [a])
        if name == 'HOL.str' and xs:
            a = self.term(xs[0])
            return ('str', a[1]) if a[0] == 'rawstr' else AP(('c', 'HOL.str'), [a])
        if name == 'List.nil' and ms and ms[0].get('k') == 'c' and ms[0].get('n') == 'HOL.char':
            return ('str', '')
        if name == 'HOL.setOf' and xs:
            p = self.term(xs[0])
            x = fresh()
            body = beta(p, [('v', x)]) if p[0] == 'lam' else AP(p, [('v', x)])
            ty = p[2] if p[0] == 'lam' else TANY
            return AP(('c', 'pred_set$GSPEC'), [LAM(x, ty, AP(('c', 'pair$,'), [('v', x), body]))])
        if re.search(r'\.match_\d+$', name):
            return self.matcher(name, xs)
        if name in self.m.lean2hol:
            hol, perm = self.m.lean2hol[name]
            args = [self.term(x) for x in xs]
            self.hol_consts[hol] += 1
            if hol == 'bool$IN':
                if cis and cis[0] == 'List.instMembership':
                    perm_args = [args[1], args[0]] if len(args) >= 2 else args
                    return AP(('c', 'LMEM'), perm_args)
            if hol == 'bool$~' and name == 'Ne':
                return ('not', ('eq', args[0], args[1])) if len(args) >= 2 else AP(('c', 'Ne'), args)
            if perm and len(args) >= len(perm) and max(perm) < len(args):
                args = [args[i] for i in perm] + args[len(perm):]
            return mk(hol, args, self)
        if self.unfoldable(name):
            v, rest = self.unfold_json(name, xs, ms, cis)
            t = self.term(v)
            return AP(t, [self.term(x) for x in rest])
        if name in ('Nat.succ',):
            return AP(('c', 'arithmetic$+'), [self.term(xs[0]), ('num', 1)])
        # unmapped constant
        self.unmapped[name] += 1
        return AP(('c', 'L:' + name), [self.term(x) for x in xs])

    def matcher(self, name, xs):
        d = self.defs.get(name, {})
        mi = d.get('matcher') or {}
        nd = mi.get('ndiscrs', 1)
        args = [None] + [self.term(x) for x in xs[1:]]
        discrs = args[1:1 + nd]
        alts = args[1 + nd:]
        if nd == 1 and len(alts) == 1:
            alt = alts[0]
            p = discrs[0]
            ap_ = (mi.get('altparams') or [0])[0]
            if ap_ == 2:
                return beta(alt, [AP(('c', 'pair$FST'), [p]), AP(('c', 'pair$SND'), [p])])
            return beta(alt, [p]) if alt[0] == 'lam' else AP(alt, [p])
        ac = d.get('altctors')
        if ac and sorted(ac) == list(range(len(alts))):
            ordered = [None] * len(alts)
            for i, c in enumerate(ac):
                ordered[c] = alts[i]
            alts = ordered
            mi = dict(mi)
            mi['altparams'] = [mi['altparams'][ac.index(c)] for c in range(len(alts))]
        # several alternatives: drop Unit lambdas of zero-parameter alternatives
        out = []
        for a, np in zip(alts, mi.get('altparams') or [1] * len(alts)):
            out.append(a[3] if (np == 0 or (a[0] == 'lam' and a[2] == ('ty', 'one$one', ()) and np == 1)) and a[0] == 'lam' else a)
        self.hol_consts['@match'] += 1
        return ('case', tuple(discrs), tuple(out))

    def statement(self, tj):
        return self.term(tj)


# ------------------------------------------------------------------ canonical string
def ph(i):
    return '\x01' + i + '\x02'


def tstr(t):
    k = t[0]
    if k == 'tv':
        return '\x03' + t[1] + '\x04'
    if k == 'fun':
        return '(' + tstr(t[1]) + '->' + tstr(t[2]) + ')'
    if k == 'ty':
        return t[1] + ('<' + ','.join(tstr(a) if a[0] != 'num' else str(a[1]) for a in t[2]) + '>' if t[2] else '')
    return str(t)


def cstr(t, wt, d):
    k = t[0]
    if k == 'v':
        return ph(t[1])
    if k == 'c':
        return t[1]
    if k == 'num':
        return str(t[1])
    if k == 'str':
        return json.dumps(t[1])
    if k == 'chr':
        return '#%d' % t[1]
    if k in ('true', 'false'):
        return k
    if k == 'unk':
        return '?' + t[1]
    if k == 'ap':
        return '(' + ' '.join([cstr(t[1], wt, d)] + [cstr(a, wt, d) for a in t[2]]) + ')'
    if k == 'lam':
        nm = 'v%d' % d
        b = cstr(t[3], wt, d + 1).replace(ph(t[1]), nm)
        return '(lam.' + b + ')'
    if k in ('all', 'ex'):
        run = []
        cur = t
        while cur[0] == k:
            run.append((cur[1], cur[2]))
            cur = cur[3]
        body = cstr(cur, wt, d + len(run))
        pos = []
        for idx, (i, ty) in enumerate(run):
            p = body.find(ph(i))
            pos.append((p if p >= 0 else 10 ** 9, tstr(ty) if wt else '', idx))
        order = sorted(range(len(run)), key=lambda x: pos[x])
        tys = []
        for rank, idx in enumerate(order):
            body = body.replace(ph(run[idx][0]), 'v%d' % (d + rank))
            tys.append(tstr(run[idx][1]) if wt else '')
        return ('A' if k == 'all' else 'E') + str(len(run)) + ('[' + ','.join(tys) + ']' if wt else '') + '{' + body + '}'
    if k == 'imp':
        return 'IMP[' + ';'.join(cstr(p, wt, d) for p in t[1]) + ']=>' + cstr(t[2], wt, d)
    if k in ('and', 'or'):
        # type variables of different conjuncts are independent (HOL4 generalises each clause separately)
        return k.upper() + '[' + ';'.join((final(cstr(p, wt, d)) if k == 'and' else cstr(p, wt, d)) for p in t[1]) + ']'
    if k == 'not':
        return '~' + cstr(t[1], wt, d)
    if k == 'eq':
        return '(' + cstr(t[1], wt, d) + '=' + cstr(t[2], wt, d) + ')'
    if k == 'ite':
        return 'ITE(' + ','.join(cstr(x, wt, d) for x in t[1:]) + ')'
    if k == 'case':
        return 'CASE[' + ';'.join(cstr(x, wt, d) for x in t[1]) + ']{' + ';'.join(cstr(x, wt, d) for x in t[2]) + '}'
    return '?' + k


def final(s):
    names = {}

    def rep(m):
        return 'T%d' % names.setdefault(m.group(1), len(names))
    return re.sub('\x03([^\x04]*)\x04', rep, s)


def free_ph(s):
    return re.findall('\x01([^\x02]*)\x02', s)


# ------------------------------------------------------------------ statistics and checks
def walk(t, f):
    f(t)
    k = t[0]
    if k == 'ap':
        walk(t[1], f)
        for a in t[2]:
            walk(a, f)
    elif k in ('lam', 'all', 'ex'):
        walk(t[3], f)
    elif k == 'imp':
        for a in t[1]:
            walk(a, f)
        walk(t[2], f)
    elif k in ('and', 'or'):
        for a in t[1]:
            walk(a, f)
    elif k == 'not':
        walk(t[1], f)
    elif k in ('eq', 'ite'):
        for a in t[1:]:
            walk(a, f)
    elif k == 'case':
        for a in t[1] + t[2]:
            walk(a, f)


def stats(t):
    s = collections.Counter()
    qseq = []
    lead = [0]
    cur = t
    while cur[0] == 'all':
        lead[0] += 1
        cur = cur[3]

    def f(x):
        k = x[0]
        if k == 'c':
            s['c:' + x[1]] += 1
        elif k in ('all', 'ex', 'lam'):
            s['binder:' + k] += 1
            qseq.append(k)
        elif k == 'imp':
            s['premises'] += len(x[1])
        elif k == 'num':
            s['num:%d' % x[1]] += 1
        elif k in ('and', 'or'):
            s[k + ':items'] += len(x[1])
        elif k in ('not', 'eq', 'ite', 'case', 'str', 'chr', 'true', 'false'):
            s[k] += 1
        elif k == 'unk':
            s['unk:' + x[1]] += 1
    walk(t, f)
    return s, ''.join({'all': 'A', 'ex': 'E', 'lam': 'L'}[q] for q in qseq), lead[0]


def unused_binders(t):
    cnt = [0]

    def f(x):
        if x[0] in ('all', 'ex'):
            used = [False]

            def g(y):
                if y[0] == 'v' and y[1] == x[1]:
                    used[0] = True
            walk(x[3], g)
            if not used[0]:
                cnt[0] += 1
    walk(t, f)
    return cnt[0]


def trivial(t):
    """vacuity markers of a canonical statement."""
    out = []
    cur = t
    while cur[0] in ('all',):
        cur = cur[3]
    prems = []
    while cur[0] == 'imp':
        prems += list(cur[1])
        cur = cur[2]
        while cur[0] == 'all':
            cur = cur[3]
    if cur[0] == 'true':
        out.append('conclusion is True')
    if cur[0] == 'eq' and cur[1] == cur[2]:
        out.append('conclusion is reflexive equality')
    if cur[0] == 'and' and all(x[0] == 'true' for x in cur[1]):
        out.append('conclusion is a conjunction of True')
    if any(p[0] == 'false' for p in prems):
        out.append('a hypothesis is False')
    for p in prems:
        if ('not', p) in prems:
            out.append('contradictory hypotheses')
            break
    return out


def first_diff(a, b, w=45):
    i = 0
    n = min(len(a), len(b))
    while i < n and a[i] == b[i]:
        i += 1
    return 'HOL4 ...%s' % a[max(0, i - 20):i + w] + ' | Lean ...%s' % b[max(0, i - 20):i + w]


def show(s):
    return re.sub('\x01([^\x02]*)\x02', 'x', s)


def diff_counters(a, b):
    out = []
    for k in sorted(set(a) | set(b)):
        if a[k] != b[k]:
            out.append('%s: HOL4 %d vs Lean %d' % (k, a[k], b[k]))
    return out


# ------------------------------------------------------------------ definition audit
def def_issues(consts, defs, mp):
    seen, stack, issues = set(), [c for c in consts if c in defs], []
    while stack:
        c = stack.pop()
        if c in seen:
            continue
        seen.add(c)
        d = defs[c]
        if d['kind'] == 'axiom':
            issues.append('axiom ' + c)
        if d['kind'] == 'opaque' and c not in mp.allow_opaque:
            issues.append('opaque ' + c)
        if d['safety'] in ('partial', 'unsafe'):
            issues.append('%s %s' % (d['safety'], c))
        for a in d['axioms']:
            if a in BAD_AXIOMS:
                issues.append('%s uses %s' % (c, 'native_decide' if a == 'Lean.ofReduceBool' else a))
            elif a not in STD_AXIOMS:
                issues.append('%s uses axiom %s' % (c, a))
        stack.extend(x for x in d['deps'] if x in defs)
    for c in consts:
        if c in ('sorryAx', 'Lean.ofReduceBool'):
            issues.append('statement mentions ' + c)
    return sorted(set(issues))


# ------------------------------------------------------------------ statement text hash
def statement_text(proj, mod, rng):
    path = os.path.join(proj, *mod.split('.')) + '.lean'
    try:
        lines = open(path, encoding='utf-8', newline='').read().replace('\r\n', '\n').split('\n')
    except OSError:
        return None
    l0, c0, l1, c1 = rng['l0'], rng['c0'], rng['l1'], rng['c1']
    seg = lines[l0 - 1:l1]
    if not seg:
        return None
    seg[-1] = seg[-1][:c1]
    seg[0] = seg[0][c0:]
    txt = '\n'.join(seg)
    depth, i = 0, 0
    while i < len(txt):
        ch = txt[i]
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif depth == 0 and txt.startswith(':=', i):
            break
        i += 1
    return txt[:i].rstrip()


def sha(txt):
    return hashlib.sha256(txt.encode('utf-8')).hexdigest()


# ------------------------------------------------------------------ main
def lean_name_for(hname, theorems):
    for ns in ('Candle', 'HOL'):
        for suffix in ('', '_thm'):
            n = '%s.%s%s' % (ns, hname, suffix)
            if n in theorems:
                return n, suffix
    return None, None


def scan(args):
    mp = Map(args.map)
    hol = [json.loads(l) for l in open(args.hol4, encoding='utf-8') if l.strip()]
    theorems, defs = {}, {}
    for l in open(args.dump, encoding='utf-8'):
        if l.startswith('@@T '):
            t = json.loads(l[4:])
            theorems[t['name']] = t
        elif l.startswith('@@D '):
            d = json.loads(l[4:])
            defs[d['name']] = d
    manifest = {}
    if args.manifest and os.path.exists(args.manifest):
        for l in open(args.manifest, encoding='utf-8'):
            p = l.rstrip('\n').split('\t')
            if len(p) >= 2:
                manifest[p[0]] = p[1]
    report, newmanifest = [], []
    used = set()
    for row in hol:
        hn = row['name']
        res = {'thy': row['thy'], 'hol4': hn, 'lean': None, 'flag': False, 'reasons': []}
        report.append(res)

        def add(cls, detail):
            res['flag'] = True
            res['reasons'].append({'class': cls, 'detail': detail})
        ln, suffix = lean_name_for(hn, theorems)
        if ln is None:
            add('missing', 'no Lean theorem named %s (tried Candle./HOL. with and without _thm)' % hn)
            continue
        used.add(ln)
        res['lean'] = ln
        th = theorems[ln]
        # ---- HOL4 side
        hc = HolConv()
        try:
            ht = hc.statement(row)
        except Exception as e:  # pragma: no cover
            add('scan-error', 'HOL4 side: %r' % e)
            continue
        # ---- Lean side
        lc = LeanConv(mp, defs)
        lt = lc.statement(th['type'])
        hs, hq, hlead = stats(ht)
        ls, lq, llead = stats(lt)
        hstr_s, lstr_s = cstr(ht, False, 0), cstr(lt, False, 0)
        hstr_f, lstr_f = cstr(ht, True, 0), cstr(lt, True, 0)
        res['hol4_form'] = show(final(hstr_f))
        res['lean_form'] = show(final(lstr_f))
        # unmapped
        if lc.unmapped:
            add('unmapped', 'Lean constants without a map row: ' + ', '.join(sorted(lc.unmapped)))
        hun = [c for c in hc.consts if c not in mp.hol2lean]
        if hun:
            add('unmapped', 'HOL4 constants without a map row: ' + ', '.join(sorted(hun)))
        # constants
        cd = diff_counters(collections.Counter({k: v for k, v in hs.items() if k.startswith('c:')}),
                           collections.Counter({k: v for k, v in ls.items() if k.startswith('c:')}))
        if cd:
            add('constants', '; '.join(cd))
        nd = diff_counters(collections.Counter({k: v for k, v in hs.items() if k.startswith(('num:', 'str', 'chr', 'unk:'))}),
                           collections.Counter({k: v for k, v in ls.items() if k.startswith(('num:', 'str', 'chr', 'unk:'))}))
        if nd:
            add('literals', '; '.join(nd))
        # binder / hypothesis / quantifier counts
        bd = diff_counters(collections.Counter({k: v for k, v in hs.items() if k.startswith('binder:')}),
                           collections.Counter({k: v for k, v in ls.items() if k.startswith('binder:')}))
        if bd:
            add('binders', '; '.join(bd))
        if hlead != llead:
            add('binders', 'leading universal binders: HOL4 %d vs Lean %d' % (hlead, llead))
        if hs['premises'] != ls['premises']:
            add('hypotheses', 'premises: HOL4 %d vs Lean %d' % (hs['premises'], ls['premises']))
        ld = diff_counters(collections.Counter({k: v for k, v in hs.items() if k in ('not', 'eq', 'ite', 'case', 'and:items', 'or:items', 'true', 'false')}),
                           collections.Counter({k: v for k, v in ls.items() if k in ('not', 'eq', 'ite', 'case', 'and:items', 'or:items', 'true', 'false')}))
        if ld:
            add('connectives', '; '.join(ld))
        if hq != lq and not bd:
            add('quantifier-order', 'binder kind sequence HOL4 %s vs Lean %s' % (hq, lq))
        # structure and types
        if final(hstr_s) != final(lstr_s):
            add('structure', first_diff(show(final(hstr_s)), show(final(lstr_s))))
        elif final(hstr_f) != final(lstr_f):
            add('binder-types', first_diff(show(final(hstr_f)), show(final(lstr_f))))
        # instance hypotheses
        need = set()
        for c in hc.consts:
            for ln_ in mp.hol2lean.get(c, ([], None))[0]:
                if ln_ in defs:
                    need.update(defs[ln_].get('insts', []))
        have = set(lc.insts)
        if have - need:
            add('instances', 'extra instance hypotheses: ' + ', '.join(sorted(have - need)))
        if need - have:
            add('instances', 'missing instance hypotheses: ' + ', '.join(sorted(need - have)))
        # vacuity
        tv, hv = trivial(lt), trivial(ht)
        for x in tv:
            if x not in hv:
                add('trivial', x)
        uu, hu = unused_binders(lt), unused_binders(ht)
        if uu != hu:
            add('trivial', 'unused quantified variables: HOL4 %d vs Lean %d' % (hu, uu))
        # definitions
        di = def_issues(sorted(lc.lean_consts), defs, mp)
        if th.get('axioms') and set(th['axioms']) - STD_AXIOMS:
            di.append('theorem uses axioms ' + ','.join(sorted(set(th['axioms']) - STD_AXIOMS)))
        if di:
            add('definitions', '; '.join(di))
        # hash
        txt = statement_text(args.project, th['mod'], th['range']) if th.get('range') else None
        if txt is not None:
            newmanifest.append((ln, sha(txt)))
            if manifest:
                if ln not in manifest:
                    add('hash', 'theorem not in manifest')
                elif manifest[ln] != sha(txt):
                    add('hash', 'statement text differs from manifest')
        elif manifest:
            add('hash', 'statement text not readable')
        res['proof_sorry'] = th.get('proof_sorry')
    extra = sorted(n for n in theorems if n not in used)
    return mp, report, theorems, extra, newmanifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dump', required=True)
    ap.add_argument('--hol4', required=True)
    ap.add_argument('--map', required=True)
    ap.add_argument('--project', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--manifest')
    ap.add_argument('--make-manifest')
    a = ap.parse_args()
    mp, report, theorems, extra, nm = scan(a)
    os.makedirs(a.out, exist_ok=True)
    flagged = [r for r in report if r['flag']]
    cls = collections.Counter()
    for r in flagged:
        for c in sorted({x['class'] for x in r['reasons']}):
            cls[c] += 1
    summary = {'statements': len(report), 'flagged': len(flagged), 'by_class': dict(cls),
               'lean_theorems_not_in_hol4_export': len(extra), 'map_status': dict(mp.status)}
    json.dump({'summary': summary, 'results': report}, open(os.path.join(a.out, 'report.json'), 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
    with open(os.path.join(a.out, 'summary.txt'), 'w', encoding='utf-8') as f:
        f.write('S0 structural scan\nstatements: %d\nflagged: %d (%.1f%%)\n' % (len(report), len(flagged), 100.0 * len(flagged) / max(1, len(report))))
        f.write('flagged statements per reason class (a statement can have several):\n')
        for c, n in sorted(cls.items(), key=lambda x: -x[1]):
            f.write('  %-18s %d\n' % (c, n))
        f.write('Lean project theorems without a HOL4 export counterpart (not scanned): %d\n' % len(extra))
        f.write('map rows by status: %s\n\n' % dict(mp.status))
        for r in report:
            f.write('%-4s %s.%s\n' % ('YES' if r['flag'] else 'no', r['thy'], r['hol4']))
            for x in r['reasons']:
                f.write('       [%s] %s\n' % (x['class'], x['detail'][:400]))
    if a.make_manifest:
        with open(a.make_manifest, 'w', encoding='utf-8', newline='\n') as f:
            for n, h in nm:
                f.write('%s\t%s\n' % (n, h))
    print('statements %d flagged %d' % (len(report), len(flagged)))
    for c, n in sorted(cls.items(), key=lambda x: -x[1]):
        print('  %-18s %d' % (c, n))


if __name__ == '__main__':
    main()
