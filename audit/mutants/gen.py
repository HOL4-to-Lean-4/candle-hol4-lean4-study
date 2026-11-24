#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Scripted mutant and decoy generator for the audit experiment (see SPEC.md).

Stages (all deterministic, seed 20261124):
  strip    comment-stripped copy of the base in WORK/stripped, built with `lake build`, sorry set compared
  enum     parse declarations, apply every scripted operator, dedupe, assign seed positions
  select   compile-check candidates lazily in seed order and sample the pool (quotas of SPEC)
  write    pool.jsonl, decoys.jsonl, README table data

Usage:  python gen.py [all|strip|enum|run] [--work DIR] [--out DIR] [--workers N] [--no-decoys]
Nothing in the base is ever written.  No network, no git.
"""
import sys, os, re, json, hashlib, shutil, subprocess, time, difflib, threading, queue, argparse
from collections import Counter, defaultdict, namedtuple
from concurrent.futures import ThreadPoolExecutor

SEED = 20261124
BASE = 'E:/ts_ws/audit_base/lean'
WORK = 'E:/ts_ws/mut_work'
OUT = 'E:/NUS/mcomp/Dissertation/candle_study/audit/mutants'
NWORK = 6
POOL_TARGET = 180                      # >= 150 required
SCOPE_SHARE = {'definition': 0.60, 'prelude': 0.25, 'statement': 0.15}
MIN_PER_FAMILY = 6
MIN_PER_HELD = 5
MAX_PER_DECL = 2
DECOY_TARGET = 60
DECOY_MIN_PER_OP = 6
LEAN_TIMEOUT = 300
MAX_OP_SHARE = 0.12                    # no single operator may exceed this share of the pool (option --max-op-share)
SORRY_AUX = False                      # option --sorry-aux: accept mutants whose only failures are proved lemmas (restated as sorry)
BIAS_SAMPLE = 1000                     # first N candidates in seed order are compiled to measure the eligibility-1 bias

BS = chr(92)

FAMILY = {
    'N1': 'numbers', 'N2': 'numbers', 'N3': 'numbers', 'N4': 'numbers',
    'C1': 'characters and strings', 'C2': 'characters and strings', 'C3': 'characters and strings',
    'O1': 'overloads',
    'H1': 'hypotheses and quantifiers', 'H2': 'hypotheses and quantifiers', 'H3': 'hypotheses and quantifiers',
    'D1': 'definitions', 'D2': 'definitions', 'D3': 'definitions', 'D4': 'definitions',
    'T1': 'type signatures',
    'U1': 'unspecified values',
    'W1': 'weakenings', 'W2': 'weakenings', 'W3': 'weakenings', 'W4': 'weakenings',
    'X1': 'held-out X1', 'X2': 'held-out X2', 'X3': 'held-out X3',
}
FAMILY_ORDER = ['numbers', 'characters and strings', 'overloads', 'hypotheses and quantifiers', 'definitions',
                'type signatures', 'unspecified values', 'weakenings']
HELD = ['X1', 'X2', 'X3']
DECOY_OPS = ['R1', 'R2', 'R3', 'R4', 'R5', 'R6']

# ----------------------------------------------------------------------------------------------
# 1. comment stripping
# ----------------------------------------------------------------------------------------------
_IDCH = re.compile(r"[A-Za-z0-9_'!?\u00c0-\u024f\u0370-\u03ff\u1d00-\u1dbf\u1f00-\u1fff\u2080-\u209c\u2100-\u214f]")
_CHRE = re.compile(r"'(\\x[0-9a-fA-F]{2}|\\u\{[0-9a-fA-F]+\}|\\.|[^\\'\n])'")


def strip_comments(src):
    """Remove block (nested), doc and line comments, aware of string and char literals."""
    out = []
    i, n = 0, len(src)
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
            out.append('\x00'); i = j
        elif src.startswith('--', i):
            j = src.find('\n', i)
            if j < 0: j = n
            out.append('\x00'); i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == BS else 1
            out.append(src[i:j + 1]); i = j + 1
        elif c == "'" and not (i > 0 and _IDCH.match(src[i - 1])):
            m = _CHRE.match(src, i)
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


def lean_files(root):
    res = []
    for dp, dn, fn in os.walk(root + '/CandleLean'):
        for f in fn:
            if f.endswith('.lean'):
                res.append(os.path.join(dp, f).replace(BS, '/'))
    res.append(root + '/CandleLean.lean')
    return sorted(res)


def run(cmd, cwd=None, env=None, timeout=None):
    p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, timeout=timeout)
    return p.returncode, p.stdout.decode('utf-8', 'replace'), p.stderr.decode('utf-8', 'replace')


def stage_strip(work, log):
    """Comment-stripped copy; build with lake; compare the sorry set with the base (KernelCheck)."""
    S = work + '/stripped'
    os.makedirs(S + '/.lake', exist_ok=True)
    for f in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'KernelCheck.lean']:
        shutil.copy2(BASE + '/' + f, S + '/' + f)
    for sub in ['packages', 'config']:
        if not os.path.isdir(S + '/.lake/' + sub):
            shutil.copytree(BASE + '/.lake/' + sub, S + '/.lake/' + sub)
    nfiles = 0
    for f in lean_files(BASE):
        rel = f[len(BASE) + 1:]
        os.makedirs(os.path.dirname(S + '/' + rel), exist_ok=True)
        with open(f, encoding='utf-8') as fh:
            t = strip_comments(fh.read())
        with open(S + '/' + rel, 'w', encoding='utf-8', newline='\n') as fh:
            fh.write(t)
        nfiles += 1
    log('stripped %d files into %s' % (nfiles, S))
    rc, so, se = run(['lake', 'build'], cwd=S)
    nsorry = so.count('declaration uses')
    log('lake build in stripped copy: rc=%d, "declaration uses sorry" warnings=%d' % (rc, nsorry))
    if rc != 0:
        raise SystemExit('stripped copy does not build:\n' + so[-2000:] + se[-2000:])
    rc, so1, se1 = run(['lake', 'env', 'lean', 'KernelCheck.lean'], cwd=S)
    rc2, so0, se0 = run(['lake', 'env', 'lean', 'KernelCheck.lean'], cwd=BASE)   # read-only use of the base
    a, b = sorted(so1.splitlines()), sorted(so0.splitlines())
    same = (a == b)
    summ = [l for l in so1.splitlines() if l.startswith('SORRY_USERS') or l.startswith('TOTAL_CANDLE')]
    log('KernelCheck stripped vs base identical: %s ; %s' % (same, summ))
    if not same:
        raise SystemExit('KernelCheck output differs between base and stripped copy')
    return {'files': nfiles, 'build_rc': rc, 'sorry_warnings': nsorry, 'kernelcheck_identical': same,
            'kernelcheck': summ}


# ----------------------------------------------------------------------------------------------
# 2. tokenizer
# ----------------------------------------------------------------------------------------------
Tok = namedtuple('Tok', 'k t s e')     # kind (id num str chr sym proj), text, start, end

SYMS = ['<;>', ':=', '=>', '->', '<-', '<|', '|>', '++', '::', '\u2203!', '<=', '>=', '!=', '==', '&&', '||',
        '..', '@[', '#[', '\u00d7\u02e2']
SYMS.sort(key=len, reverse=True)
_ID = r"(?:[^\W\d]|_)(?:\w|['!?])*"
_IDRE = re.compile(r"\.?" + _ID + r"(?:\." + r"(?:" + _ID + r"|\d+))*")
_NUMRE = re.compile(r"\d+")
_STRRE = re.compile(r'"(?:[^"\\]|\\.)*"', re.S)
OPEN = {'(': ')', '[': ']', '{': '}', '\u27e8': '\u27e9', '\u2983': '\u2984', '@[': ']', '#[': ']'}
CLOSE = {')', ']', '}', '\u27e9', '\u2984'}


def tokenize(text):
    toks = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1; continue
        if c == '"':
            m = _STRRE.match(text, i)
            j = m.end() if m else n
            toks.append(Tok('str', text[i:j], i, j)); i = j; continue
        if c == "'" and not (i > 0 and _IDCH.match(text[i - 1])):
            m = _CHRE.match(text, i)
            if m:
                toks.append(Tok('chr', m.group(0), i, m.end())); i = m.end(); continue
        if c.isdigit():
            m = _NUMRE.match(text, i)
            toks.append(Tok('num', m.group(0), i, m.end())); i = m.end(); continue
        if c == '.' and i + 1 < n and text[i + 1].isdigit() and i > 0 and not text[i - 1].isspace():
            m = _NUMRE.match(text, i + 1)
            toks.append(Tok('proj', '.' + m.group(0), i, m.end())); i = m.end(); continue
        if (c.isalpha() or c == '_' or (c == '.' and i + 1 < n and (text[i + 1].isalpha() or text[i + 1] == '_'))) \
                and c not in '\u03bb':
            m = _IDRE.match(text, i)
            if m:
                toks.append(Tok('id', m.group(0), i, m.end())); i = m.end(); continue
        for sy in SYMS:
            if text.startswith(sy, i):
                toks.append(Tok('sym', sy, i, i + len(sy))); i += len(sy); break
        else:
            toks.append(Tok('sym', c, i, i + 1)); i += 1
    return toks


KEYWORDS = {'fun', 'then', 'else', 'with', 'match', 'if', 'let', 'in', 'at', 'by', 'from', 'do', 'have', 'show',
            'termination_by', 'decreasing_by', 'where', 'deriving', 'using', 'open', 'true', 'false_', 'return',
            'for', 'mut', 'λ', 'at', 'generalizing', 'only'}
STOP_ATOM = KEYWORDS | {':=', '=>', '|', ',', ':', ';', '→', '->', '↔', '∧', '∨', '=', '≠', '<', '>', '≤', '≥', '∈',
                         '∉', '++', '::', '+', '-', '*', '/', '%', '^', '×', '∘', '¬', '∀', '∃', '∃!', '⊆', '<|', '|>',
                         '▸', '←', '$', '&&', '||', '==', '!=', '<=', '>='}
# NB: STOP_ATOM keeps symbol tokens that end an application argument list.


class Decl:
    """One top-level declaration of the stripped base."""

    def __init__(self, module, path, ns, text, start, line):
        self.module, self.path, self.ns = module, path, list(ns)
        self.text, self.start, self.line = text, start, line
        self.toks = tokenize(text)
        T = self.toks
        # depth and matching brackets
        self.d, self.match = [], {}
        stack, dep = [], 0
        for i, t in enumerate(T):
            if t.k == 'sym' and t.t in OPEN:
                self.d.append(dep); stack.append(i); dep += 1
            elif t.k == 'sym' and t.t in CLOSE:
                dep = max(0, dep - 1); self.d.append(dep)
                if stack:
                    j = stack.pop(); self.match[j] = i; self.match[i] = j
            else:
                self.d.append(dep)
        # line / col per token
        self.col, self.ls = [], []
        ls_idx = [0] + [m.end() for m in re.finditer(r"\n", text)]
        import bisect
        for t in T:
            k = bisect.bisect_right(ls_idx, t.s) - 1
            self.col.append(t.s - ls_idx[k])
            self.ls.append(t.s == ls_idx[k] + (len(text[ls_idx[k]:t.s]) - len(text[ls_idx[k]:t.s].lstrip())) and
                           text[ls_idx[k]:t.s].strip() == '')
        self.parse_header()
        self.prot = set()
        self.mark_protected()
        self.analyze()

    # ---- header
    def parse_header(self):
        T = self.toks
        i = 0
        self.attrs = ''
        while i < len(T) and T[i].t == '@[':
            j = self.match.get(i, i)
            self.attrs += ' '.join(t.t for t in T[i + 1:j]) + ' '
            i = j + 1
        self.private = False
        while i < len(T) and T[i].t in ('private', 'protected', 'noncomputable', 'partial', 'unsafe', 'nonrec'):
            if T[i].t == 'private': self.private = True
            i += 1
        self.kind = T[i].t if i < len(T) else '?'
        self.kw_i = i
        self.name = None
        self.name_i = None
        if i + 1 < len(T) and T[i + 1].k == 'id' and self.kind in ('def', 'abbrev', 'theorem', 'lemma', 'inductive',
                                                                     'structure', 'opaque', 'axiom', 'instance', 'class'):
            self.name = T[i + 1].t
            self.name_i = i + 1

    @property
    def short(self):
        return self.name.split('.')[-1] if self.name else None

    @property
    def full(self):
        return '.'.join(self.ns + [self.name]) if self.name else '<anon@%d>' % self.line

    def txt(self, a, b):
        """source text of tokens a..b-1 inclusive span"""
        return self.text[self.toks[a].s:self.toks[b - 1].e]

    # ---- protected tokens
    def mark_protected(self):
        T, d = self.toks, self.d
        n = len(T)
        for i, t in enumerate(T):
            if t.k == 'id' and t.t == 'by':
                j = i + 1
                while j < n and d[j] >= d[i] and not (T[j].t in CLOSE and d[j] < d[i]):
                    if d[j] < d[i]: break
                    j += 1
                # tokens inside (and the closing bracket excluded)
                for k in range(i, min(j, n)):
                    self.prot.add(k)
            elif t.t == '|' and t.k == 'sym':
                j = i + 1
                while j < n and d[j] >= d[i]:
                    if d[j] == d[i] and T[j].t in ('=>', '|', ':='):
                        break
                    j += 1
                if j < n and T[j].t == '=>' and d[j] == d[i]:
                    for k in range(i, j):
                        self.prot.add(k)
            elif t.k == 'id' and t.t in ('fun',):
                j = i + 1
                while j < n and d[j] >= d[i]:
                    if d[j] == d[i] and T[j].t in ('=>', ':='):
                        break
                    j += 1
                if j < n and T[j].t == '=>' and d[j] == d[i]:
                    for k in range(i, j):
                        self.prot.add(k)
            elif t.k == 'sym' and t.t in ('∀', '∃', '∃!'):
                j = i + 1
                while j < n and d[j] >= d[i]:
                    if d[j] == d[i] and T[j].t == ',':
                        break
                    j += 1
                if j < n and T[j].t == ',' and d[j] == d[i]:
                    for k in range(i, j):
                        self.prot.add(k)

    # ---- structure
    def top_find(self, a, b, texts, depth=None):
        if depth is None:
            depth = self.d[a] if a < len(self.toks) else 0
        r = []
        for i in range(a, min(b, len(self.toks))):
            if self.d[i] == depth and self.toks[i].t in texts and self.toks[i].k in ('sym', 'id'):
                r.append(i)
        return r

    def analyze(self):
        T = self.toks
        n = len(T)
        self.sorry_stmt = False
        self.ranges = []        # expression ranges (a,b) for generic token ops
        self.stmt = None        # theorem statement range / ctor type ranges
        self.colon = None
        self.assign = None
        self.arms_start = None
        self.tail = n
        self.sig = None
        self.prop_valued = False
        self.type_range = None
        self.ctors = []
        self.body = None
        if self.kind in ('def', 'abbrev', 'theorem', 'lemma', 'opaque', 'instance'):
            i0 = (self.name_i + 1) if self.name_i is not None else self.kw_i + 1
            # tail
            for i in range(i0, n):
                if T[i].k == 'id' and T[i].t in ('termination_by', 'decreasing_by') and self.d[i] == 0:
                    self.tail = i; break
            end = self.tail
            cols = self.top_find(i0, end, {':'})
            assigns = self.top_find(i0, end, {':='})
            self.colon = cols[0] if cols else None
            self.assign = assigns[0] if assigns else None
            if self.assign is not None and self.colon is not None and self.colon > self.assign:
                self.colon = None
            sig_end = self.assign if self.assign is not None else end
            if self.assign is None:
                bars = [i for i in self.top_find(i0, end, {'|'}) if self.colon is None or i > self.colon]
                if bars:
                    self.arms_start = bars[0]; sig_end = bars[0]
            self.sig = (i0, sig_end)
            if self.colon is not None:
                self.type_range = (self.colon + 1, sig_end)
                if self.type_range[1] > self.type_range[0] and T[sig_end - 1].t == 'Prop':
                    self.prop_valued = True
            else:
                self.type_range = None
            if self.assign is not None:
                self.body = (self.assign + 1, end)
            elif self.arms_start is not None:
                self.body = (self.arms_start, end)
            if self.kind in ('theorem', 'lemma'):
                if self.body is not None:
                    toks_body = [t.t for t in T[self.body[0]:self.body[1]]]
                    self.sorry_stmt = (toks_body == ['by', 'sorry'])
                if self.type_range:
                    self.stmt = self.type_range
                    self.ranges = [self.type_range]
            elif self.kind in ('def', 'abbrev'):
                if self.body:
                    self.ranges = [self.body]
        elif self.kind == 'inductive':
            wh = [i for i in range(n) if T[i].t == 'where' and self.d[i] == 0]
            if wh:
                hdr = (self.name_i + 1, wh[0])
                self.prop_valued = (wh[0] - 1 >= 0 and T[wh[0] - 1].t == 'Prop')
                self.sig = hdr
                bars = [i for i in range(wh[0] + 1, n) if T[i].t == '|' and self.d[i] == 0]
                dv = [i for i in range(wh[0] + 1, n) if T[i].k == 'id' and T[i].t == 'deriving' and self.d[i] == 0]
                endc = dv[0] if dv else n
                for k, b in enumerate(bars):
                    e = bars[k + 1] if k + 1 < len(bars) else endc
                    if b >= endc: continue
                    cn = T[b + 1].t if b + 1 < n else None
                    cols = self.top_find(b + 2, e, {':'})
                    c = cols[0] if cols else None
                    self.ctors.append({'bar': b, 'end': e, 'name': cn, 'colon': c,
                                       'type': (c + 1, e) if c is not None else None})
                self.ranges = [c['type'] for c in self.ctors if c['type']]

    # ---- arms
    def arm_groups(self, a=None, b=None):
        """Return list of groups; each group = list of arms (bar_i, arrow_i, rhs_a, rhs_b)."""
        T, d = self.toks, self.d
        groups = []
        if self.body is None:
            return groups
        a0, b0 = self.body
        if a is not None: a0, b0 = a, b
        starts = []
        if self.arms_start is not None and a is None:
            starts.append((self.arms_start - 1 if self.arms_start > 0 else 0, self.arms_start))
        for i in range(a0, b0):
            if T[i].k == 'id' and T[i].t == 'with' and i + 1 < len(T) and T[i + 1].t == '|':
                starts.append((i, i + 1))
        for (w, fb) in starts:
            base = d[fb]
            fb_ls = self.ls[fb]
            colfirst = self.col[fb]
            bars = [fb]
            j = fb + 1
            end = b0
            while j < b0:
                if d[j] < base:
                    end = j; break
                if self.ls[j] and self.col[j] < colfirst and fb_ls and T[j].t != '|':
                    end = j; break
                if self.ls[j] and self.col[j] < colfirst and fb_ls and T[j].t == '|':
                    end = j; break
                if T[j].t == '|' and d[j] == base and (not fb_ls or (self.ls[j] and self.col[j] == colfirst)):
                    bars.append(j)
                j += 1
            arms = []
            for k, bj in enumerate(bars):
                ae = bars[k + 1] if k + 1 < len(bars) else end
                arrow = None
                for q in range(bj + 1, ae):
                    if T[q].t == '=>' and d[q] == base:
                        arrow = q; break
                if arrow is None: arms = []; break
                arms.append({'bar': bj, 'arrow': arrow, 'rhs': (arrow + 1, ae), 'end': ae})
            if len(arms) >= 1:
                groups.append(arms)
        return groups

    def mutable(self, i):
        return i not in self.prot

    def expr_tokens(self):
        for (a, b) in self.ranges:
            for i in range(a, b):
                if self.mutable(i):
                    yield i


def split_decls(module, path, text):
    """Split a stripped file into declarations; also tracks namespaces."""
    lines = text.split('\n')
    cmd_re = re.compile(r"^(?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                        r"(def|abbrev|theorem|lemma|inductive|structure|class|instance|opaque|axiom|example)\b")
    other_re = re.compile(r"^(namespace|end|open|universe|variable|section|noncomputable|export|import|set_option|"
                          r"attribute|mutual|macro|syntax|notation|local|scoped)\b")
    offs = []
    pos = 0
    for ln in lines:
        offs.append(pos); pos += len(ln) + 1
    decls, ns = [], []
    cur = None
    def close(cur, endline):
        if cur is None: return
        s_line, ns_snapshot = cur
        e = endline
        while e > s_line and lines[e - 1].strip() == '':
            e -= 1
        t = '\n'.join(lines[s_line:e])
        decls.append(Decl(module, path, ns_snapshot, t, offs[s_line], s_line + 1))
    for li, ln in enumerate(lines):
        if ln == '' or ln[0] in ' \t':
            continue
        if cmd_re.match(ln):
            close(cur, li)
            cur = (li, ns)
            continue
        m = other_re.match(ln)
        if m:
            close(cur, li); cur = None
            kw = m.group(1)
            if kw == 'namespace':
                ns = ns + [ln.split()[1]]
            elif kw == 'end':
                parts = ln.split()
                if len(parts) > 1 and ns and ns[-1] == parts[1]:
                    ns = ns[:-1]
            continue
        # col-0 continuation (termination_by, decreasing_by, deriving ...) belongs to cur
    close(cur, len(lines))
    return decls


def load_modules(root):
    """Parse the stripped project: modules, imports, declarations."""
    mods = {}
    for f in lean_files(root):
        rel = f[len(root) + 1:-5]
        name = rel.replace('/', '.')
        with open(f, encoding='utf-8') as fh:
            text = fh.read()
        imports = re.findall(r"^import\s+(\S+)", text, re.M)
        mods[name] = {'path': f, 'rel': rel + '.lean', 'text': text, 'imports': imports, 'decls': []}
    for name, m in mods.items():
        if name == 'CandleLean': continue
        m['decls'] = split_decls(name, m['path'], m['text'])
    return mods


def dependents_chain(mods, name):
    """Module `name` followed by all modules that (transitively) import it, in topological order; root excluded."""
    rev = defaultdict(set)
    for n, m in mods.items():
        for i in m['imports']:
            rev[i].add(n)
    seen, st = {name}, [name]
    while st:
        x = st.pop()
        for y in rev[x]:
            if y not in seen:
                seen.add(y); st.append(y)
    seen.discard('CandleLean')
    order, done = [], set()
    def visit(x):
        if x in done: return
        done.add(x)
        for i in mods[x]['imports']:
            if i in seen: visit(i)
        order.append(x)
    for x in sorted(seen): visit(x)
    return order


# ----------------------------------------------------------------------------------------------
# 3. operators
# ----------------------------------------------------------------------------------------------
class Cand:
    __slots__ = ('decl', 'op', 'edits', 'tag', 'note', 'key', 'new_decl', 'new_file', 'rank', 'pos', 'scope', 'label',
                 'family', 'old_span', 'new_span')

    def __init__(self, decl, op, edits, tag, note=''):
        self.decl, self.op, self.edits, self.tag, self.note = decl, op, edits, tag, note
        self.family = FAMILY.get(op, 'decoy')


def apply_edits(text, edits):
    out = text
    for (a, b, new) in sorted(edits, key=lambda e: -e[0]):
        out = out[:a] + new + out[b:]
    return out


NUM_ARITY_SKIP = set()
FP_STATS = {'seen': 0, 'dropped': 0, 'by_op': Counter()}
ARROWS = ('→', '->')


class Ops:
    """Operator implementations.  Each yields Cand objects for one declaration."""

    def __init__(self, mods):
        self.mods = mods
        self.all_decls = [d for m in mods.values() for d in m['decls']]
        self.known = set()
        self.prop_defs = set()
        self.ctor_names = {'some', 'none'}
        for d in self.all_decls:
            if d.kind == 'inductive':
                for c in d.ctors:
                    if c['name']: self.ctor_names.add(c['name'])
            if d.name and d.kind in ('def', 'abbrev', 'inductive', 'opaque', 'structure', 'theorem'):
                self.known.add(d.short)
            if d.kind == 'inductive':
                for c in d.ctors:
                    self.known.add(c['name'])
            if d.name and d.kind in ('def', 'abbrev') and d.prop_valued:
                self.prop_defs.add(d.short)
            if d.name and d.kind == 'inductive' and d.prop_valued:
                self.prop_defs.add(d.short)

    # ---------------- helpers
    # ---------------- parenthesis discipline: add parentheses only where Lean needs them
    def atomic_text(self, text):
        toks = tokenize(text)
        if len(toks) <= 1:
            return True
        if toks[0].t in OPEN:
            depth = 0
            for k, t in enumerate(toks):
                if t.t in OPEN: depth += 1
                elif t.t in CLOSE:
                    depth -= 1
                    if depth == 0:
                        return k == len(toks) - 1
        return False

    def in_arg_pos(self, d, i):
        T = d.toks
        if i <= 0: return False
        p = T[i - 1]
        if p.k in ('num', 'str', 'chr', 'proj'): return True
        if p.k == 'id' and p.t not in STOP_ATOM: return True
        return p.t in CLOSE

    def ends_expr(self, d, j):
        T = d.toks
        if j >= len(T): return True
        t = T[j]
        return t.t in CLOSE or t.t in (',', ':=', '=>', 'then', 'else', '|', 'with', 'termination_by', 'decreasing_by')

    def wrap(self, d, i, j, text):
        """text replaces tokens [i, j); parenthesise only if it is not atomic and the context can absorb it."""
        if self.atomic_text(text):
            return text
        if not self.in_arg_pos(d, i) and self.ends_expr(d, j):
            return text
        return '(' + text + ')'

    def branch_wrap(self, text):
        toks = tokenize(text)
        for t in toks:
            if t.k == 'id' and t.t in ('match', 'fun', 'let', 'have', 'by', 'do', 'show'):
                return '(' + text + ')'
        return text

    def neg_wrap(self, d, a, b, text):
        if self.atomic_text(text):
            return text
        ops = [p for p in self.prop_ops(d, a, b)]
        if ops or any(d.toks[q].t in ('∀', '∃', 'fun', 'if') for q in range(a, b)):
            return '(' + text + ')'
        return text

    # ---------------- match-arm patterns (for D4 and decoy arm reorder)
    def parse_pat(self, d, a, b):
        T = d.toks
        if a >= b: return None
        D = d.d[a]
        cons = [i for i in range(a, b) if d.d[i] == D and T[i].t == '::']
        if cons:
            l = self.parse_pat(d, a, cons[0]); r = self.parse_pat(d, cons[0] + 1, b)
            if l is None or r is None: return None
            return ('ctor', 'cons', [l, r])
        plus = [i for i in range(a, b) if d.d[i] == D and T[i].t == '+']
        if len(plus) == 1 and b == plus[0] + 2 and T[plus[0] + 1].k == 'num':
            return ('succ', int(T[plus[0] + 1].t))
        if T[a].t in ('(', '\u27e8', '[') and d.match.get(a) == b - 1:
            inner = (a + 1, b - 1)
            parts, st = [], inner[0]
            for q in range(inner[0], inner[1]):
                if d.d[q] == d.d[a] + 1 and T[q].t == ',':
                    parts.append((st, q)); st = q + 1
            if inner[1] > inner[0]:
                parts.append((st, inner[1]))
            nodes = [self.parse_pat(d, x, y) for (x, y) in parts]
            if any(n is None for n in nodes): return None
            if T[a].t == '[':
                res = ('ctor', 'nil', [])
                for n in reversed(nodes):
                    res = ('ctor', 'cons', [n, res])
                return res
            if T[a].t == '(' and len(nodes) == 1:
                return nodes[0]
            return ('ctor', 'tuple%d' % len(nodes), nodes)
        if b - a == 1:
            t = T[a]
            if t.k == 'num': return ('lit', int(t.t))
            if t.t == '_': return ('var',)
            if t.k == 'id':
                nm = t.t.lstrip('.')
                if t.t.startswith('.') or nm.split('.')[-1] in self.ctor_names:
                    return ('ctor', nm.split('.')[-1], [])
                return ('var',)
            return None
        head = T[a]
        if head.k == 'id' and (head.t.lstrip('.').split('.')[-1] in self.ctor_names or head.t.startswith('.')):
            args = []
            j = a + 1
            while j < b:
                if T[j].t in OPEN:
                    k = d.match.get(j)
                    if k is None or k >= b: return None
                    n = self.parse_pat(d, j, k + 1); j = k + 1
                else:
                    n = self.parse_pat(d, j, j + 1); j += 1
                if n is None: return None
                args.append(n)
            return ('ctor', head.t.lstrip('.').split('.')[-1], args)
        return None

    def pat_cols(self, d, arm):
        T = d.toks
        a, b = arm['bar'] + 1, arm['arrow']
        parts, st = [], a
        for q in range(a, b):
            if d.d[q] == d.d[arm['bar']] and T[q].t == ',':
                parts.append((st, q)); st = q + 1
        parts.append((st, b))
        nodes = [self.parse_pat(d, x, y) for (x, y) in parts]
        return None if any(n is None for n in nodes) else nodes

    def must_overlap(self, p, q):
        if p[0] == 'var' or q[0] == 'var': return True
        if p[0] == 'lit' and q[0] == 'lit': return p[1] == q[1]
        if p[0] == 'lit' and q[0] == 'succ': return p[1] >= q[1]
        if p[0] == 'succ' and q[0] == 'lit': return q[1] >= p[1]
        if p[0] == 'succ' and q[0] == 'succ': return True
        if p[0] == 'ctor' and q[0] == 'ctor':
            if p[1] != q[1] or len(p[2]) != len(q[2]): return False
            return all(self.must_overlap(x, y) for x, y in zip(p[2], q[2]))
        return False

    def must_disjoint(self, p, q):
        if p[0] == 'var' or q[0] == 'var': return False
        if p[0] == 'lit' and q[0] == 'lit': return p[1] != q[1]
        if p[0] == 'lit' and q[0] == 'succ': return p[1] < q[1]
        if p[0] == 'succ' and q[0] == 'lit': return q[1] < p[1]
        if p[0] == 'succ' and q[0] == 'succ': return False
        if p[0] == 'ctor' and q[0] == 'ctor':
            if p[1] != q[1]: return True
            if len(p[2]) != len(q[2]): return False
            return any(self.must_disjoint(x, y) for x, y in zip(p[2], q[2]))
        return False

    def arms_overlap(self, d, A, B):
        ca, cb = self.pat_cols(d, A), self.pat_cols(d, B)
        if ca is None or cb is None or len(ca) != len(cb): return None
        return all(self.must_overlap(x, y) for x, y in zip(ca, cb))

    def arms_disjoint(self, d, A, B):
        ca, cb = self.pat_cols(d, A), self.pat_cols(d, B)
        if ca is None or cb is None or len(ca) != len(cb): return None
        return any(self.must_disjoint(x, y) for x, y in zip(ca, cb))

    def arm_total(self, d, A):
        ca = self.pat_cols(d, A)
        return ca is not None and all(n[0] == 'var' for n in ca)

    def edit_tok(self, d, i, new):
        t = d.toks[i]
        return (t.s, t.e, new)

    def atoms_after(self, d, i, limit):
        """consecutive application arguments after head token i (as (a,b) token-index spans)."""
        T = d.toks
        args = []
        j = i + 1
        while j < limit:
            t = T[j]
            if d.d[j] != d.d[i]:
                break
            if t.k in ('id',) and t.t in STOP_ATOM:
                break
            if t.k == 'sym' and t.t in OPEN and not (t.t == '{' ):
                k = d.match.get(j)
                if k is None or k >= limit: break
                # named argument (x := e) : skip as non-swappable but continue
                if any(T[q].t == ':=' for q in range(j + 1, k) if d.d[q] == d.d[j] + 1):
                    args.append(None); j = k + 1; continue
                args.append((j, k + 1)); j = k + 1; continue
            if t.k in ('id', 'num', 'str', 'chr', 'proj'):
                if t.k == 'id' and t.t.startswith('.') and False:
                    break
                args.append((j, j + 1)); j += 1; continue
            break
        return args

    def prop_ops(self, d, a, b):
        """Positions of depth-D connectives in [a,b) before the first binder-like keyword."""
        D = d.d[a]
        res = []
        stop = {'∀', '∃', '∃!', 'fun', 'λ', 'if', 'match', 'let', 'then', 'else', 'by', 'have', 'show'}
        for i in range(a, b):
            t = d.toks[i]
            if d.d[i] != D: continue
            if t.t in stop and i > a:
                break
            if t.t in ('↔', '→', '∨', '∧') and t.k == 'sym':
                res.append(i)
        return res

    def split_at(self, d, a, b, positions):
        segs, s = [], a
        for p in positions:
            segs.append((s, p)); s = p + 1
        segs.append((s, b))
        return segs

    # ---------------- Prop walk: W1 W2 W3 W4 H1 H2 H3
    def walk(self, d, a, b, sign, out, depth_guard=0):
        T = d.toks
        if a >= b or depth_guard > 40:
            return
        # unwrap outer parentheses
        if T[a].t == '(' and d.match.get(a) == b - 1:
            return self.walk(d, a + 1, b - 1, sign, out, depth_guard + 1)
        # quantifier prefix
        if T[a].t in ('∀', '∃', '∃!') and T[a].k == 'sym':
            comma = None
            for i in range(a + 1, b):
                if d.d[i] == d.d[a] and T[i].t == ',':
                    comma = i; break
            if comma is None: return
            if T[a].t in ('∀', '∃'):
                out.append(('quant', a, sign))
            self.walk_conj_move(d, a, comma, b, sign, out)
            return self.walk(d, comma + 1, b, sign, out, depth_guard + 1)
        ops = self.prop_ops(d, a, b)
        def texts(kind): return [p for p in ops if T[p].t == kind]
        iffs = texts('↔')
        if iffs:
            out.append(('iff', iffs, a, b, sign))
            for (x, y) in self.split_at(d, a, b, iffs):
                self.walk(d, x, y, 0, out, depth_guard + 1)
            return
        imps = texts('→')
        if imps:
            segs = self.split_at(d, a, b, imps)
            out.append(('imp', segs, imps, sign))
            for k, (x, y) in enumerate(segs):
                self.walk(d, x, y, -sign if k < len(segs) - 1 else sign, out, depth_guard + 1)
            return
        ors = texts('∨')
        if ors:
            for (x, y) in self.split_at(d, a, b, ors):
                self.walk(d, x, y, sign, out, depth_guard + 1)
            return
        ands = texts('∧')
        if ands:
            segs = self.split_at(d, a, b, ands)
            out.append(('and', segs, ands, sign))
            for (x, y) in segs:
                self.walk(d, x, y, sign, out, depth_guard + 1)
            return
        if T[a].t == '¬' and T[a].k == 'sym':
            return self.walk(d, a + 1, b, -sign, out, depth_guard + 1)
        out.append(('atom', a, b, sign))

    def walk_conj_move(self, d, qa, comma, b, sign, out):
        """H3 sites: quantifier whose body is a conjunction and the variable occurs in a sibling conjunct."""
        T = d.toks
        names = [T[i].t for i in range(qa + 1, comma) if T[i].k == 'id' and T[i].t not in ('Type', 'Prop')
                 and d.d[i] == d.d[qa]]
        if not names: return
        ands = [p for p in self.prop_ops(d, comma + 1, b) if T[p].t == '∧']
        if ands and not [p for p in self.prop_ops(d, comma + 1, b) if T[p].t in ('→', '↔', '∨')]:
            segs = self.split_at(d, comma + 1, b, ands)
            # move binder inside the first conjunct: (Q x, A) ∧ B ; applicable when a name occurs in some later conjunct
            later = ' '.join(d.txt(x, y) for (x, y) in segs[1:])
            occ = [nm for nm in names if re.search(r"(?<![\w'])" + re.escape(nm) + r"(?![\w'])", later)]
            if occ:
                out.append(('h3in', qa, comma, segs, sign))
        # pull a parenthesised quantified conjunct outside: (Q x, A) ∧ B -> Q x, A ∧ B   (handled in 'and' walk below)

    def prop_regions(self, d):
        res = []
        if d.kind in ('theorem', 'lemma') and d.sorry_stmt and d.stmt:
            res.append(('stmt', d.stmt[0], d.stmt[1], 1))
        elif d.kind in ('def', 'abbrev') and d.prop_valued and d.body:
            groups = d.arm_groups() if d.arms_start is not None else []
            if groups:
                for arm in groups[0]:
                    res.append(('arm', arm['rhs'][0], arm['rhs'][1], 1))
            else:
                res.append(('body', d.body[0], d.body[1], 1))
        elif d.kind == 'inductive' and d.prop_valued:
            for c in d.ctors:
                if c['type']:
                    res.append(('ctor', c['type'][0], c['type'][1], 1))
        return res

    def ops_prop(self, d):
        T = d.toks
        cands = []
        for (kind, a, b, sign) in self.prop_regions(d):
            ev = []
            self.walk(d, a, b, sign, ev)
            top_imp_done = False
            for e in ev:
                if e[0] == 'and':
                    _, segs, ands, sg = e
                    # W1: drop one conjunct
                    for k in range(len(segs)):
                        if k + 1 < len(segs):
                            ed1 = (T[segs[k][0]].s, T[segs[k + 1][0]].s, '')
                        else:
                            ed1 = (T[segs[k - 1][1] - 1].e, T[segs[k][1] - 1].e, '')
                        cands.append(Cand(d, 'W1', [ed1],
                                          'silent' if sg == 1 else 'visible', 'drop conjunct %d of %d' % (k + 1, len(segs))))
                    # W3: ∧ -> ∨
                    for p in ands:
                        cands.append(Cand(d, 'W3', [self.edit_tok(d, p, '∨')],
                                          'silent' if sg == 1 else 'visible', 'and->or'))
                    # H3 (pull outward): parenthesised quantified conjunct (Q x, A) ∧ B with x occurring in B
                    for k, (x, y) in enumerate(segs[:-1]):
                        if T[x].t == '(' and d.match.get(x) == y - 1 and T[x + 1].t in ('∀', '∃'):
                            q = x + 1
                            comma = None
                            for i in range(q + 1, y - 1):
                                if d.d[i] == d.d[q] and T[i].t == ',':
                                    comma = i; break
                            if comma is None: continue
                            names = [T[i].t for i in range(q + 1, comma) if T[i].k == 'id']
                            later = ' '.join(d.txt(x2, y2) for (x2, y2) in segs[k + 1:])
                            if any(re.search(r"(?<![\w'])" + re.escape(nm) + r"(?![\w'])", later) for nm in names):
                                qtxt = d.txt(q, comma + 1)
                                inner = d.txt(comma + 1, y - 1)
                                rest = ' ∧ '.join([inner] + [d.txt(x2, y2) for (x2, y2) in segs[k + 1:]])
                                new = qtxt + ' ' + rest
                                cands.append(Cand(d, 'H3', [(T[segs[k][0]].s, T[segs[-1][1] - 1].e, new)], 'visible',
                                                  'move binder outside conjunct'))
                elif e[0] == 'iff':
                    _, iffs, aa, bb, sg = e
                    for p in iffs:
                        cands.append(Cand(d, 'W4', [self.edit_tok(d, p, '→')],
                                          'silent' if sg == 1 else 'visible', 'iff->imp'))
                elif e[0] == 'imp':
                    _, segs, imps, sg = e
                    for k in range(len(segs) - 1):
                        # H1: drop premise k
                        x, y = segs[k]
                        sx = T[x].s
                        sy = T[segs[k + 1][0]].s
                        cands.append(Cand(d, 'H1', [(sx, sy, '')], 'visible' if sg == 1 else 'silent',
                                          'drop premise %d of %d' % (k + 1, len(segs) - 1)))
                elif e[0] == 'quant':
                    _, qi, sg = e
                    q = T[qi].t
                    new = '∃' if q == '∀' else '∀'
                    silent = (q == '∀' and sg == 1) or (q == '∃' and sg == -1)
                    cands.append(Cand(d, 'H2', [self.edit_tok(d, qi, new)], 'silent' if silent else 'visible',
                                      'quantifier swap'))
                elif e[0] == 'h3in':
                    _, qa, comma, segs, sg = e
                    # Q x, A ∧ B -> (Q x, A) ∧ B   (x of B now unbound / captured)
                    qtxt = d.txt(qa, comma + 1)
                    first = d.txt(segs[0][0], segs[0][1])
                    new = '(' + qtxt + ' ' + first + ')'
                    cands.append(Cand(d, 'H3', [(T[qa].s, T[segs[0][1] - 1].e, new)], 'visible',
                                      'move binder inside conjunct'))
                elif e[0] == 'atom':
                    _, aa, bb, sg = e
                    # W4 on Prop-equality of two relation calls:  P x = Q y  ->  P x -> Q y
                    eqs = [i for i in range(aa, bb) if d.d[i] == d.d[aa] and T[i].t == '=' and T[i].k == 'sym']
                    if len(eqs) == 1:
                        lhs_head = T[aa].t
                        rhs_head = T[eqs[0] + 1].t if eqs[0] + 1 < bb else ''
                        if lhs_head in self.prop_defs or rhs_head in self.prop_defs:
                            cands.append(Cand(d, 'W4', [self.edit_tok(d, eqs[0], '→')],
                                              'silent' if sg == 1 else 'visible', 'prop-eq->imp'))
            # H1 on hypothesis binders (theorem statements only)
            if kind == 'stmt' and d.sig:
                for i in range(d.sig[0], d.sig[1]):
                    if T[i].t == '(' and d.d[i] == 0 and d.match.get(i) and T[i + 1].k == 'id' \
                            and re.match(r"^h[0-9a-z_']*$", T[i + 1].t) and T[i + 2].t == ':':
                        j = d.match[i]
                        cands.append(Cand(d, 'H1', [(T[i].s, T[j].e, '')], 'visible', 'drop hypothesis binder'))
            # W2: add a hypothesis
            cands += self.ops_w2(d, kind, a, b)
        return cands

    def binder_vars(self, d):
        """(name, type text) of binders of theorem/def signature and of the leading quantifier prefix."""
        T = d.toks
        res = []
        if d.sig:
            i = d.sig[0]
            e = d.colon if d.colon is not None else d.sig[1]
            while i < e:
                if T[i].t in ('(', '{') and d.match.get(i) is not None:
                    j = d.match[i]
                    cols = [q for q in range(i + 1, j) if T[q].t == ':' and d.d[q] == d.d[i] + 1]
                    if cols:
                        ty = d.txt(cols[0] + 1, j)
                        for q in range(i + 1, cols[0]):
                            if T[q].k == 'id': res.append((T[q].t, ty))
                    i = j + 1
                else:
                    i += 1
        return res

    def ops_w2(self, d, kind, a, b):
        T = d.toks
        cands = []
        if kind not in ('stmt', 'body'):
            return cands
        vars_ = self.binder_vars(d)
        # leading quantifier prefix: find insertion point after the last prefix comma, collect ∀ vars
        ins = a
        qvars = []
        while ins < b and T[ins].t in ('∀', '∃') and T[ins].k == 'sym':
            comma = None
            for i in range(ins + 1, b):
                if d.d[i] == d.d[ins] and T[i].t == ',':
                    comma = i; break
            if comma is None: break
            i = ins + 1
            while i < comma:
                if T[i].t == '(' and d.match.get(i):
                    j = d.match[i]
                    cols = [q for q in range(i + 1, j) if T[q].t == ':']
                    if cols:
                        ty = d.txt(cols[0] + 1, j)
                        for q in range(i + 1, cols[0]):
                            if T[q].k == 'id': qvars.append((T[q].t, ty))
                    i = j + 1
                elif T[i].k == 'id':
                    qvars.append((T[i].t, '?')); i += 1
                else:
                    i += 1
            ins = comma + 1
            if T[ins - 1].t == ',' and ins < b and T[ins].t in ('∀', '∃'):
                continue
        allv = vars_ + qvars
        prem = []
        for (v, ty) in allv:
            tys = ty.strip()
            if tys.startswith('List') or tys.endswith('list') or tys == 'string':
                prem.append('%s ≠ []' % v)
            elif tys == 'Nat':
                prem.append('0 < %s' % v)
        seen = set()
        for k1 in range(len(allv)):
            for k2 in range(k1 + 1, len(allv)):
                if allv[k1][1] == allv[k2][1] and allv[k1][1] != '?' :
                    prem.append('%s ≠ %s' % (allv[k1][0], allv[k2][0]))
        qs = [v for (v, ty) in qvars]
        if len(qs) >= 2:
            prem.append('%s ≠ %s' % (qs[0], qs[1]))
        for p in prem:
            if p in seen: continue
            seen.add(p)
            if any(d.toks[q].t == '↔' for q in self.prop_ops(d, ins, b)):
                edits = [(T[ins].s, T[ins].s, '%s → (' % p), (T[b - 1].e, T[b - 1].e, ')')]
            else:
                edits = [(T[ins].s, T[ins].s, '%s → ' % p)]
            cands.append(Cand(d, 'W2', edits, 'silent', 'add hypothesis'))
            if len(seen) >= 6: break
        return cands

    # ---------------- generic token operators
    def ops_tokens(self, d):
        T = d.toks
        cands = []
        if not d.ranges or d.kind in ('instance',):
            return cands
        # restrict generic token operators to non-signature expression ranges
        is_def = d.kind in ('def', 'abbrev')
        for i in d.expr_tokens():
            t = T[i]
            if t.k == 'num' and int(t.t) < 1000:
                v = int(t.t)
                cands.append(Cand(d, 'N1', [self.edit_tok(d, i, str(v + 1))], 'visible', '+1'))
                if v > 0:
                    cands.append(Cand(d, 'N1', [self.edit_tok(d, i, str(v - 1))], 'visible', '-1'))
            if t.k == 'sym':
                m = {'<': '≤', '≤': '<', '>': '≥', '≥': '>', '<=': '<', '>=': '>'}
                if t.t in m:
                    cands.append(Cand(d, 'N2', [self.edit_tok(d, i, m[t.t])], 'visible', 'strictness'))
                if t.t == '+' :
                    cands.append(Cand(d, 'N3', [self.edit_tok(d, i, '-')], 'visible', '+ to -'))
                if t.t == '-':
                    cands.append(Cand(d, 'N3', [self.edit_tok(d, i, '+')], 'visible', '- to +'))
            if t.k in ('str', 'chr'):
                body = t.t[1:-1]
                if body and BS not in body:
                    for pos in sorted({0, len(body) - 1}):
                        ch = body[pos]
                        if ch.isalpha():
                            nc = chr(ord(ch) + 1) if ch.lower() not in 'z' else chr(ord(ch) - 1)
                        elif ch.isdigit():
                            nc = str((int(ch) + 1) % 10)
                        else:
                            nc = 'a'
                        nb = body[:pos] + nc + body[pos + 1:]
                        q = t.t[0]
                        cands.append(Cand(d, 'C1', [self.edit_tok(d, i, q + nb + q)], 'visible', 'char %d' % pos))
            if t.k == 'id':
                nm = t.t
                for (x, y) in C2_PAIRS:
                    if nm == x: cands.append(Cand(d, 'C2', [self.edit_tok(d, i, y)], 'visible', 'strict/non-strict'))
                    if nm == y: cands.append(Cand(d, 'C2', [self.edit_tok(d, i, x)], 'visible', 'strict/non-strict'))
                for (x, y) in O1_PAIRS:
                    if nm == x: cands.append(Cand(d, 'O1', [self.edit_tok(d, i, y)], 'visible', x + '->' + y))
                    if nm == y: cands.append(Cand(d, 'O1', [self.edit_tok(d, i, x)], 'visible', y + '->' + x))
                if nm in ('implode', 'explode', 'strlit', 'str', 'mls', 'mlstring.implode'):
                    j = i + 1
                    if j < len(T) and (T[j].k in ('id', 'str', 'num') or T[j].t in ('(', '⟨')):
                        args = self.atoms_after(d, i, d.ranges[0][1] if False else len(T))
                        if args and args[0]:
                            a0, b0 = args[0]
                            if T[a0].t == '(' and not self.in_arg_pos(d, i) and self.ends_expr(d, b0) \
                                    and not self.atomic_text(d.txt(a0 + 1, b0 - 1)):
                                ed = (T[i].s, T[b0 - 1].e, d.txt(a0 + 1, b0 - 1))
                            else:
                                ed = (T[i].s, T[a0].s, '')
                            cands.append(Cand(d, 'C3', [ed], 'visible', 'drop conversion ' + nm))
            if t.k == 'sym' and t.t in ('∪', '∩'):
                cands.append(Cand(d, 'O1', [self.edit_tok(d, i, '∩' if t.t == '∪' else '∪')], 'visible', 'union/inter'))
        cands += self.ops_ite(d)
        cands += self.ops_arms(d)
        cands += self.ops_calls(d)
        cands += self.ops_n4(d)
        cands += self.ops_x(d)
        return cands

    # ---- numbers: N4 base case literal
    def ops_n4(self, d):
        cands = []
        if d.kind not in ('def', 'abbrev') or d.arms_start is None:
            return cands
        T = d.toks
        groups = d.arm_groups()
        if not groups: return cands
        for arm in groups[0]:
            a, b = arm['rhs']
            body_names = {T[i].t for i in range(a, b)}
            if d.short in body_names:
                continue
            for i in range(a, b):
                if T[i].k == 'num' and T[i].t in ('0', '1') and d.mutable(i):
                    cands.append(Cand(d, 'N4', [self.edit_tok(d, i, '1' if T[i].t == '0' else '0')], 'visible',
                                      'base case %s' % T[i].t))
        return cands

    # ---- if/else and arms: D2 D4
    def if_parts(self, d, i, limit):
        T, dd = d.toks, d.d
        D = dd[i]
        j = i + 1
        level = 0
        then_i = None
        while j < limit:
            if dd[j] < D: return None
            if dd[j] == D and T[j].k == 'id':
                if T[j].t == 'if': level += 1
                elif T[j].t == 'then':
                    if level == 0: then_i = j; break
                    level -= 1
            j += 1
        if then_i is None: return None
        level = 0
        else_i = None
        j = then_i + 1
        while j < limit:
            if dd[j] < D: return None
            if dd[j] == D and T[j].k == 'id':
                if T[j].t == 'if': level += 1
                elif T[j].t == 'else':
                    if level == 0: else_i = j; break
                    level -= 1
            j += 1
        if else_i is None: return None
        # end of else-branch
        k = else_i + 1
        while k < limit:
            if dd[k] < D: break
            if dd[k] == D:
                if T[k].t in (',', ':=', 'with', '|', 'termination_by', 'decreasing_by') and T[k].t != '':
                    break
                if T[k].k == 'id' and T[k].t in ('then', 'else', 'termination_by', 'decreasing_by'):
                    break
                if d.ls[k] and T[k].t == '|':
                    break
            k += 1
        return (then_i, else_i, k)

    def ops_ite(self, d):
        cands = []
        T = d.toks
        for (a, b) in d.ranges:
            for i in range(a, b):
                if T[i].k == 'id' and T[i].t == 'if' and d.mutable(i):
                    r = self.if_parts(d, i, b)
                    if not r: continue
                    then_i, else_i, end = r
                    cond = d.txt(i + 1, then_i)
                    tx = d.txt(then_i + 1, else_i)
                    ex = d.txt(else_i + 1, end)
                    if chr(10) in tx or chr(10) in ex: continue          # multi-line branches (let chains) are not swapped by script
                    new = 'if ' + cond + ' then ' + self.branch_wrap(ex) + ' else ' + self.branch_wrap(tx)
                    cands.append(Cand(d, 'D2', [(T[i].s, T[end - 1].e, new)], 'visible', 'swap if branches'))
        return cands

    def ops_arms(self, d):
        cands = []
        if d.kind not in ('def', 'abbrev'):
            return cands
        T = d.toks
        for gi, arms in enumerate(d.arm_groups()):
            if len(arms) < 2: continue
            # D2: swap rhs of adjacent arms
            for k in range(len(arms) - 1):
                A, B = arms[k], arms[k + 1]
                ta = d.txt(A['rhs'][0], A['rhs'][1]); tb = d.txt(B['rhs'][0], B['rhs'][1])
                if ta == tb: continue
                cands.append(Cand(d, 'D2', [(T[A['rhs'][0]].s, T[A['rhs'][1] - 1].e, tb),
                                            (T[B['rhs'][0]].s, T[B['rhs'][1] - 1].e, ta)], 'visible',
                                  'swap arm results %d,%d' % (k + 1, k + 2)))
            # D4: reorder two adjacent arms whose patterns certainly overlap (otherwise the swap is equivalent)
            for k in range(len(arms) - 1):
                A, B = arms[k], arms[k + 1]
                if not self.arms_overlap(d, A, B): continue
                ta = d.txt(A['bar'], A['end']); tb = d.txt(B['bar'], B['end'])
                if ta == tb: continue
                sep = d.text[T[A['end'] - 1].e:T[B['bar']].s]
                cands.append(Cand(d, 'D4', [(T[A['bar']].s, T[B['end'] - 1].e, tb + sep + ta)], 'visible',
                                  'reorder overlapping arms %d,%d' % (k + 1, k + 2)))
            # D4: remove an arm that a later total (all-variable) arm then covers
            for k in range(len(arms) - 1):
                A = arms[k]
                if not any(self.arm_total(d, arms[j]) for j in range(k + 1, len(arms))): continue
                e = T[arms[k + 1]['bar']].s
                cands.append(Cand(d, 'D4', [(T[A['bar']].s, e, '')], 'visible', 'remove arm %d (covered by later wildcard)' % (k + 1)))
        return cands

    # ---- calls: D1 D3
    def ops_calls(self, d):
        cands = []
        if d.kind not in ('def', 'abbrev'):
            return cands
        T = d.toks
        for (a, b) in d.ranges:
            for i in range(a, b):
                t = T[i]
                if t.k != 'id' or not d.mutable(i): continue
                head = t.t.split('.')[-1] if '.' in t.t and not t.t.startswith('.') else t.t
                if (head in self.known or t.t == d.name or t.t == d.short) and t.t not in STOP_ATOM:
                    args = self.atoms_after(d, i, b)
                    # D1: swap adjacent args
                    for k in range(len(args) - 1):
                        A, B = args[k], args[k + 1]
                        if A is None or B is None: continue
                        if any(not d.mutable(q) for q in range(A[0], B[1])): continue
                        ta, tb = d.txt(*A), d.txt(*B)
                        if ta == tb: continue
                        cands.append(Cand(d, 'D1', [(T[A[0]].s, T[A[1] - 1].e, tb), (T[B[0]].s, T[B[1] - 1].e, ta)],
                                          'visible', 'swap args %d,%d of %s' % (k + 1, k + 2, t.t)))
                    # D3: recursive call, replace one argument by a sibling
                    if (t.t == d.name or t.t == d.short) and len(args) >= 2:
                        texts = [d.txt(*A) if A else None for A in args]
                        for k, A in enumerate(args):
                            if A is None: continue
                            for j2, tj in enumerate(texts):
                                if j2 == k or tj is None or tj == texts[k]: continue
                                cands.append(Cand(d, 'D3', [(T[A[0]].s, T[A[1] - 1].e, tj)], 'visible',
                                                  'recursive arg %d := arg %d' % (k + 1, j2 + 1)))
        return cands

    # ---- T1
    def ops_t1(self, d):
        cands = []
        T = d.toks
        if d.kind not in ('def', 'abbrev', 'theorem', 'lemma', 'inductive'):
            return cands
        if d.kind in ('theorem', 'lemma') and not d.sorry_stmt:
            return cands
        lo, hi = 0, len(T)
        if d.kind in ('def', 'abbrev', 'theorem', 'lemma'):
            lo = d.name_i + 1 if d.name_i is not None else 1
            hi = d.assign if d.assign is not None else (d.arms_start if d.arms_start is not None else len(T))
        elif d.kind == 'inductive':
            lo = d.name_i + 1
        for i in range(lo, hi):
            t = T[i]
            if t.k == 'id' and t.t in T1_MAP and i > 0 and T[i - 1].t == ':':
                nxt = T[i + 1].t if i + 1 < len(T) else ''
                if nxt not in (')', '}', ',', ':=', '', '\u27e9', ']'):
                    continue
                # the variable(s) of this binder: identifiers between the opening bracket / quantifier and the colon
                j = i - 2
                names = []
                while j >= 0 and T[j].k == 'id':
                    names.append(T[j].t); j -= 1
                if not names: continue
                used = [q for q in range(i + 1, len(T)) if T[q].k == 'id' and T[q].t in names]
                if not used: continue                      # T1 only on a variable the declaration uses
                for r in T1_MAP[t.t]:
                    cands.append(Cand(d, 'T1', [self.edit_tok(d, i, r)], 'visible', '%s->%s' % (t.t, r)))
        return cands

    # ---- U1
    def ops_u1(self, d):
        cands = []
        T = d.toks
        if d.kind == 'opaque' and d.name:
            if d.assign is not None:
                wit = d.body
                wtxt = d.txt(*wit)
                if 'Classical.choose' not in wtxt:
                    cands.append(Cand(d, 'U1', [self.edit_tok(d, d.kw_i, 'def')], 'silent',
                                      'opaque -> def exposing witness'))
                    # fallback constant swapped
                    for i in range(wit[0], wit[1]):
                        if T[i].t == 'default' and T[i].k == 'id':
                            cands.append(Cand(d, 'U1', [self.edit_tok(d, d.kw_i, 'def'), self.edit_tok(d, i, 'ARB')],
                                              'silent', 'opaque -> def, fallback default := ARB'))
                        if T[i].t == 'Classical.choice' and i + 1 < len(T) and T[i + 1].t == 'inferInstance':
                            cands.append(Cand(d, 'U1', [self.edit_tok(d, d.kw_i, 'def'),
                                                        (T[i].s, T[i + 1].e, 'ARB')], 'silent',
                                              'opaque -> def, fallback choice := ARB'))
                        if T[i].k == 'num' and i > wit[0] and T[i - 1].t == '⟨' and d.mutable(i) is not None:
                            v = int(T[i].t)
                            cands.append(Cand(d, 'U1', [self.edit_tok(d, d.kw_i, 'def'), self.edit_tok(d, i, str(v + 1))],
                                              'silent', 'opaque -> def, fallback value %d := %d' % (v, v + 1)))
            elif d.name != 'ARB':
                # constant without body
                ty = None
                if d.colon is not None:
                    cands.append(Cand(d, 'U1', [(T[d.sig[1] - 1].e, T[d.sig[1] - 1].e, ' := ARB'),
                                                self.edit_tok(d, d.kw_i, 'def')], 'silent',
                                     'opaque constant -> ARB'))
        if d.kind in ('def', 'abbrev'):
            for i in range(len(T)):
                if T[i].t == '@Classical.epsilon' and i + 3 < len(T):
                    args = self.atoms_after(d, i, len(T))
                    if len(args) >= 3 and args[1] and T[args[1][0]].t == '⟨':
                        inner = d.txt(args[1][0] + 1, args[1][1] - 1)
                        cands.append(Cand(d, 'U1', [(T[i].s, T[args[2][1] - 1].e, self.wrap(d, i, args[2][1], inner))], 'silent',
                                          'Hilbert choice replaced by its witness'))
        return cands

    # ---- X operators (held out)
    def ops_x(self, d):
        cands = []
        T = d.toks
        names = {t.t for t in T if t.k == 'id'}
        maps = {'UPDATE', 'FUPDATE', 'UPDATE_LIST', 'ALOOKUP', 'FLOOKUP', 'alist_to_fmap', 'REV_ASSOCD', 'FEMPTY'}
        capt = {'VSUBST', 'INST_CORE', 'VARIANT', 'VFREE_IN', 'INST', 'RESULT', 'CLASH', 'Result', 'Clash',
                'IS_CLASH', 'IS_RESULT', 'VARIANT_PRIMES', 'fresh', 'bv_names', 'rename_bvars', 'simple_subst'}
        for i in d.expr_tokens():
            t = T[i]
            if t.k == 'id':
                # X1: update / union order
                if (names & maps):
                    if t.t in ('.reverse', 'List.reverse'):
                        pass
                    if t.t == '.reverse':
                        cands.append(Cand(d, 'X1', [self.edit_tok(d, i, '')], 'visible', 'drop reverse (update order)'))
                    if t.t in ('List.foldl',): cands.append(Cand(d, 'X1', [self.edit_tok(d, i, 'List.foldr')], 'visible', 'foldl->foldr'))
                    if t.t in ('List.foldr', '.foldr'):
                        cands.append(Cand(d, 'X1', [self.edit_tok(d, i, t.t.replace('foldr', 'foldl'))], 'visible', 'foldr->foldl'))
                    if t.t in ('UPDATE', 'FUPDATE'):
                        args = self.atoms_after(d, i, len(T))
                        # nested update chain: swap the two updates
                        for k, A in enumerate(args):
                            if A and T[A[0]].t == '(' and T[A[0] + 1].t == t.t:
                                inner_args = self.atoms_after(d, A[0] + 1, A[1] - 1)
                                if t.t == 'FUPDATE' and len(inner_args) >= 2 and len(args) >= 2 and k == 0:
                                    f_in, p_in = inner_args[0], inner_args[1]
                                    p_out = args[1]
                                    if f_in and p_in and p_out:
                                        cands.append(Cand(d, 'X1', [(T[p_in[0]].s, T[p_in[1] - 1].e, d.txt(*p_out)),
                                                                    (T[p_out[0]].s, T[p_out[1] - 1].e, d.txt(*p_in))],
                                                          'visible', 'swap nested FUPDATE'))
                    if t.t in ('ALOOKUP', 'alist_to_fmap', 'FLOOKUP', 'REV_ASSOCD'):
                        cands.append(Cand(d, 'X1', [self.edit_tok(d, i, '(fun l => List.reverse l |> ' + t.t + ')')]
                                          if False else [], 'visible', 'x'))
                if t.t in ('ALOOKUP', 'alist_to_fmap'):
                    args = self.atoms_after(d, i, len(T))
                    a0 = args[0] if t.t == 'alist_to_fmap' else (args[0] if args else None)
                    if a0 and T[a0[0]].t == '(':
                        k = a0[1] - 1
                        pp = [q for q in range(a0[0] + 1, k) if T[q].t == '++' and d.d[q] == d.d[a0[0]] + 1]
                        if len(pp) == 1:
                            L = d.txt(a0[0] + 1, pp[0]); R = d.txt(pp[0] + 1, k)
                            cands.append(Cand(d, 'X1', [(T[a0[0] + 1].s, T[k - 1].e, R + ' ++ ' + L)], 'visible',
                                              'swap lookup list order'))
                    if a0 and T[a0[0]].t == '(' and T[a0[0] + 1].t not in ('List.reverse', '.reverse'):
                        cands.append(Cand(d, 'X1', [(T[a0[0]].s, T[a0[1] - 1].e, '(List.reverse ' + d.txt(*a0) + ')')],
                                          'visible', 'reverse lookup list'))
                if t.t == 'ALOOKUP' or t.t == 'alist_to_fmap':
                    pass
                # X2: capture / substitution condition
                if names & capt:
                    for (x, y) in X2_PAIRS:
                        if t.t == x: cands.append(Cand(d, 'X2', [self.edit_tok(d, i, y)], 'visible', x + '->' + y))
                        if t.t == y: cands.append(Cand(d, 'X2', [self.edit_tok(d, i, x)], 'visible', y + '->' + x))
                    if t.t == 'VFREE_IN' or t.t == 'VARIANT':
                        args = self.atoms_after(d, i, len(T))
                        if len(args) >= 2 and args[0] and args[1]:
                            ta, tb = d.txt(*args[0]), d.txt(*args[1])
                            if ta != tb and t.t == 'VFREE_IN':
                                cands.append(Cand(d, 'X2', [(T[args[0][0]].s, T[args[0][1] - 1].e, tb),
                                                            (T[args[1][0]].s, T[args[1][1] - 1].e, ta)], 'visible',
                                                  'swap VFREE_IN arguments'))
                        if t.t == 'VARIANT' and args and args[0]:
                            cands.append(Cand(d, 'X2', [(T[args[0][0]].s, T[args[0][1] - 1].e, '[]')], 'visible',
                                              'avoid-list emptied'))
                    if t.t in ('INST_CORE', 'VSUBST'):
                        args = self.atoms_after(d, i, len(T))
                        if args and args[0] and d.txt(*args[0]) != '[]':
                            cands.append(Cand(d, 'X2', [(T[args[0][0]].s, T[args[0][1] - 1].e, '[]')], 'visible',
                                              'env := []'))
            if (names & maps) and 'if' in names and t.k == 'sym' and t.t in ('=', '≠') and d.kind in ('def', 'abbrev')                     and any(T[q].t == 'if' for q in range(max(0, i - 8), i)):
                cands.append(Cand(d, 'X1', [self.edit_tok(d, i, '≠' if t.t == '=' else '=')], 'visible',
                                  'key test negated in lookup/update'))
            if (names & maps) and t.k == 'id' and t.t == 'if' and d.mutable(i):
                r = self.if_parts(d, i, len(T))
                if r:
                    then_i, else_i, end = r
                    cond = d.txt(i + 1, then_i)
                    ex_, tx_ = d.txt(else_i + 1, end), d.txt(then_i + 1, else_i)
                    if chr(10) in ex_ or chr(10) in tx_: continue
                    new = 'if ' + cond + ' then ' + self.branch_wrap(ex_) + ' else ' + self.branch_wrap(tx_)
                    cands.append(Cand(d, 'X1', [(T[i].s, T[end - 1].e, new)], 'visible', 'swap lookup/update branches'))
            if (names & maps) and t.k == 'id' and t.t in self.known and t.t in maps:
                args = self.atoms_after(d, i, len(T))
                for k in range(len(args) - 1):
                    A, B = args[k], args[k + 1]
                    if A and B and d.txt(*A) != d.txt(*B):
                        cands.append(Cand(d, 'X1', [(T[A[0]].s, T[A[1] - 1].e, d.txt(*B)), (T[B[0]].s, T[B[1] - 1].e, d.txt(*A))],
                                          'visible', 'swap args of ' + t.t))
            if t.k == 'sym' and (names & capt):
                if t.t == '≠':
                    cands.append(Cand(d, 'X2', [self.edit_tok(d, i, '=')], 'visible', '≠ to ='))
                if t.t == '¬':
                    cands.append(Cand(d, 'X2', [self.edit_tok(d, i, '')], 'visible', 'drop ¬'))
                if t.t in ('∉',):
                    cands.append(Cand(d, 'X2', [self.edit_tok(d, i, '∈')], 'visible', '∉ to ∈'))
            if t.k == 'sym' and (names & capt) and t.t == '=':
                pass
            # X3: list order / multiplicity (anywhere)
            if t.k == 'sym' and t.t == '++':
                lo, hi = self.operand_span(d, i)
                if lo is not None:
                    L = d.txt(lo[0], lo[1]); R = d.txt(hi[0], hi[1])
                    if L != R:
                        cands.append(Cand(d, 'X3', [(T[lo[0]].s, T[hi[1] - 1].e, R + ' ++ ' + L)], 'visible', 'swap ++ operands'))
                    cands.append(Cand(d, 'X3', [(T[lo[0]].s, T[hi[1] - 1].e, L + ' ++ ' + L)], 'visible', 'duplicate ++ operand'))
            if t.k == 'id':
                if t.t in ('EVERY', 'EXISTS'):
                    cands.append(Cand(d, 'X3', [self.edit_tok(d, i, 'EXISTS' if t.t == 'EVERY' else 'EVERY')], 'visible',
                                      'EVERY/EXISTS'))
                if t.t in ('.reverse', 'List.reverse'):
                    cands.append(Cand(d, 'X3', [self.edit_tok(d, i, '')] if t.t == '.reverse' else
                                      [self.edit_tok(d, i, 'id')], 'visible', 'drop reverse'))
                if t.t in ('SNOC',):
                    cands.append(Cand(d, 'X3', [self.edit_tok(d, i, 'List.cons')], 'visible', 'SNOC->cons'))
                if t.t in ('FILTER', 'List.filter'):
                    pass
                if t.t in ('GENLIST',):
                    pass
                if t.t in ('ZIP',):
                    pass
                if t.t in ('SEG',):
                    pass
                if t.t in ('List.take', '.take'):
                    cands.append(Cand(d, 'X3', [self.edit_tok(d, i, t.t.replace('take', 'drop'))], 'visible', 'take->drop'))
                if t.t in ('List.drop', '.drop'):
                    cands.append(Cand(d, 'X3', [self.edit_tok(d, i, t.t.replace('drop', 'take'))], 'visible', 'drop->take'))
                if t.t in ('List.map', '.map'):
                    pass
            if t.k == 'sym' and t.t == '::':
                lo, hi = self.operand_span(d, i)
                if lo is not None:
                    L = d.txt(lo[0], lo[1]); R = d.txt(hi[0], hi[1])
                    cands.append(Cand(d, 'X3', [(T[lo[0]].s, T[hi[1] - 1].e, R + ' ++ [' + L + ']')], 'visible',
                                      'cons to snoc'))
        return [c for c in cands if c.edits]

    def operand_span(self, d, i):
        """Left and right operand token spans of an infix operator at token i (atoms or bracketed groups)."""
        T = d.toks
        # right
        j = i + 1
        if j >= len(T): return None, None
        if T[j].t in OPEN:
            k = d.match.get(j)
            if k is None: return None, None
            hi = (j, k + 1)
        elif T[j].k in ('id', 'num', 'str', 'chr') and T[j].t not in KEYWORDS:
            hi = (j, j + 1)
            # allow simple application x.foo or id only
        else:
            return None, None
        # left
        j = i - 1
        if j < 0: return None, None
        if T[j].t in CLOSE:
            k = d.match.get(j)
            if k is None: return None, None
            lo = (k, j + 1)
        elif T[j].k in ('id', 'num', 'str', 'chr', 'proj') and T[j].t not in KEYWORDS:
            lo = (j, j + 1)
        else:
            return None, None
        # operands must be single atoms (not arguments of a larger application)
        if lo[0] > 0 and (T[lo[0] - 1].k in ('id',) and T[lo[0] - 1].t not in STOP_ATOM and T[lo[0] - 1].t not in KEYWORDS
                          and d.d[lo[0] - 1] == d.d[lo[0]]):
            return None, None
        return lo, hi

    # ---------------- entry
    def all_for(self, d):
        if d.name is None or d.name.startswith('Aux.') or d.name.startswith('Aux'):
            if d.name is None or d.name.startswith('Aux.'):
                return []
        if d.kind in ('structure', 'class', 'instance', 'lemma', 'axiom', 'example', '?'):
            return []
        if d.kind in ('theorem', 'lemma') and not d.sorry_stmt:
            return []
        out = []
        out += self.ops_prop(d)
        out += self.ops_tokens(d)
        out += self.ops_t1(d)
        out += self.ops_u1(d)
        return out


C2_PAIRS = [('char_lt', 'char_le'), ('string_lt', 'string_le'), ('mlstring_lt', 'mlstring_le')]
O1_PAIRS = [('pair', 'upair'), ('LESS', 'GREATER'), ('binary_union', 'product'), ('LIST_TO_SET', 'FDOM'),
            ('LIST_TO_SET', 'FRANGE'), ('FLOOKUP', 'ALOOKUP'), ('HD', 'LAST'), ('TL', 'FRONT'), ('MAX', 'MIN'),
            ('EVEN', 'ODD'), ('type_cmp', 'term_cmp'), ('type_lt', 'term_lt'), ('Tyvar', 'Tyapp')]
X2_PAIRS = [('Result', 'Clash'), ('IS_CLASH', 'IS_RESULT'), ('RESULT', 'CLASH')]
T1_MAP = {'Nat': ['Int', 'char'], 'mlstring': ['string', 'type'], 'string': ['mlstring', 'Nat'],
          'type': ['term', 'mlstring'], 'term': ['type', 'mlstring'], 'char': ['Nat'], 'ordering': ['Bool'],
          'Bool': ['Nat']}


# ----------------------------------------------------------------------------------------------
# 4. decoy operators
# ----------------------------------------------------------------------------------------------
class DecoyOps:
    def __init__(self, ops):
        self.ops = ops
        self.abbrevs = {}
        for d in ops.all_decls:
            if d.kind in ('abbrev',) or (d.kind == 'def' and 'reducible' in d.attrs):
                if d.name and d.body and d.assign is not None:
                    params = []
                    ok = True
                    if d.sig:
                        i = d.sig[0]
                        e = d.colon if d.colon is not None else d.sig[1]
                        while i < e:
                            if d.toks[i].t in ('(', '{', '[') and d.match.get(i):
                                j = d.match[i]
                                if d.toks[i].t == '(':
                                    cols = [q for q in range(i + 1, j) if d.toks[q].t == ':']
                                    if cols:
                                        for q in range(i + 1, cols[0]):
                                            if d.toks[q].k == 'id': params.append(d.toks[q].t)
                                    else: ok = False
                                i = j + 1
                            else:
                                ok = False; break
                    if ok:
                        self.abbrevs[d.short] = (params, d.txt(*d.body), d)

    def all_for(self, d):
        if d.name is None or d.name.startswith('Aux.'): return []
        if d.kind not in ('def', 'abbrev', 'theorem', 'inductive'): return []
        if d.kind == 'theorem' and not d.sorry_stmt: return []
        if d.kind == 'inductive' and not d.prop_valued: return []
        out = []
        out += self.r1(d)
        out += self.r2(d)
        out += self.r3(d)
        out += self.r4(d)
        out += self.r5(d)
        out += self.r6(d)
        return out

    # R1: rename a bound variable of a ∀/∃/fun binder
    def r1(self, d):
        T = d.toks
        cands = []
        used = {t.t for t in T if t.k == 'id'}
        for i, t in enumerate(T):
            if d.kind in ('def', 'abbrev', 'theorem'):
                if not (d.assign is None or i > (d.sig[0] if d.sig else 0)): continue
            if t.k == 'sym' and t.t in ('∀', '∃') or (t.k == 'id' and t.t == 'fun'):
                endb = None
                for j in range(i + 1, len(T)):
                    if d.d[j] == d.d[i] and T[j].t in (',', '=>'):
                        endb = j; break
                    if d.d[j] < d.d[i]: break
                if endb is None: continue
                # body extent: until closing bracket of enclosing group or end of range
                bend = len(T)
                for j in range(endb + 1, len(T)):
                    if d.d[j] < d.d[i]:
                        bend = j; break
                simple = [j for j in range(i + 1, endb) if T[j].k == 'id' and d.d[j] == d.d[i]
                          and T[j].t.isidentifier()]
                binder_ids = [j for j in range(i + 1, endb) if T[j].k == 'id']
                # only plain binders without type ascription or with simple ones
                if not simple: continue
                v = T[simple[0]]
                if len(v.t) > 6 or '.' in v.t: continue
                new = v.t + '_1'
                if new in used: continue
                # occurrences of v inside binder and body
                ed = []
                for j in range(i + 1, bend):
                    if T[j].k == 'id' and T[j].t == v.t:
                        ed.append(self.ops.edit_tok(d, j, new))
                    elif T[j].k == 'id' and T[j].t.startswith(v.t + '.') and False:
                        pass
                # skip if v is shadowed by a nested binder of the same name
                nested = [j for j in range(endb + 1, bend) if T[j].k == 'id' and T[j].t == v.t and
                          T[j - 1].t in ('∀', '∃', 'fun', '(')]
                if nested: continue
                if len(ed) >= 2:
                    cands.append(Cand(d, 'R1', ed, 'decoy', 'rename %s' % v.t))
        # rename theorem/def explicit binder (x : T) is a signature change; skip
        return cands

    # R2: commute ∧ ∨ = ↔ between atoms
    def r2(self, d):
        T = d.toks
        cands = []
        for (a, b) in d.ranges:
            for i in range(a, b):
                t = T[i]
                if t.k == 'sym' and t.t in ('∧', '∨', '↔', '=') :
                    lo, hi = self.span_around(d, i, a, b)
                    if lo is None: continue
                    L, R = d.txt(*lo), d.txt(*hi)
                    if L == R: continue
                    cands.append(Cand(d, 'R2', [(T[lo[0]].s, T[hi[1] - 1].e, R + ' ' + t.t + ' ' + L)], 'decoy',
                                      'commute %s' % t.t))
        return cands

    def span_around(self, d, i, a, b):
        """operands of infix op i: maximal runs of tokens at the same depth bounded by connectives/delimiters."""
        T = d.toks
        D = d.d[i]
        delim = {'∧', '∨', '↔', '→', ',', ':=', '=>', '|', '∀', '∃', '∃!', 'then', 'else', 'with', 'if', 'fun', '¬',
                 'termination_by', 'decreasing_by', 'by', ';'}
        j = i - 1
        while j >= a and not (d.d[j] == D and T[j].t in delim):
            if d.d[j] < D: break
            j -= 1
        lo = j + 1
        k = i + 1
        while k < b and not (d.d[k] == D and T[k].t in delim):
            if d.d[k] < D: break
            k += 1
        hi_end = k
        if lo >= i or hi_end <= i + 1: return None, None
        # operands must not contain other relational/arith operators at depth D to stay safe
        rel = {'=', '≠', '<', '>', '≤', '≥', '∈', '∉', '++', '::', '+', '-', '*', '/', '%', '×', '∘', '▸'}
        for q in list(range(lo, i)) + list(range(i + 1, hi_end)):
            if d.d[q] == D and T[q].t in rel and T[q].k == 'sym': return None, None
        # the operator must be the only connective of its kind at this level: if it is a ∧/∨ chain only adjacent swap
        return (lo, i), (i + 1, hi_end)

    # R3: swap two independent quantified variables in ∀ x y, / ∃ x y,
    def r3(self, d):
        T = d.toks
        cands = []
        for i, t in enumerate(T):
            if t.k == 'sym' and t.t in ('∀', '∃'):
                comma = None
                for j in range(i + 1, len(T)):
                    if d.d[j] == d.d[i] and T[j].t == ',':
                        comma = j; break
                    if d.d[j] < d.d[i]: break
                if comma is None: continue
                ids = [j for j in range(i + 1, comma)]
                if all(T[j].k == 'id' for j in ids) and len(ids) >= 2:
                    names = [T[j].t for j in ids]
                    if len(set(names)) == len(names):
                        new = ' '.join([names[1], names[0]] + names[2:])
                        cands.append(Cand(d, 'R3', [(T[ids[0]].s, T[ids[-1]].e, new)], 'decoy', 'swap binders'))
                # nested ∀ x, ∀ y,
                if comma + 1 < len(T) and T[comma + 1].t == t.t and len(ids) >= 1 and all(T[j].k == 'id' for j in ids):
                    c2 = None
                    for j in range(comma + 2, len(T)):
                        if d.d[j] == d.d[i] and T[j].t == ',':
                            c2 = j; break
                    if c2 and all(T[j].k == 'id' for j in range(comma + 2, c2)):
                        o = d.txt(i, comma + 1)
                        inn = d.txt(comma + 1, c2 + 1)
                        cands.append(Cand(d, 'R3', [(T[i].s, T[c2].e, inn + ' ' + o)], 'decoy', 'swap nested quantifiers'))
        return cands

    # R4: eta / beta
    def r4(self, d):
        T = d.toks
        cands = []
        for (a, b) in d.ranges:
            for i in range(a, b):
                t = T[i]
                if not d.mutable(i): continue
                if t.k == 'id' and i > a and T[i - 1].t in ('List.map', '.map', 'MAP', 'FILTER', 'EVERY', 'EXISTS', 'LIST_REL',
                                                          'List.filter', 'List.foldr', 'OPT_MMAP', 'MAPi', 'UNCURRY'):
                    if t.t in self.ops.known and t.t[0] != '_':
                        cands.append(Cand(d, 'R4', [self.ops.edit_tok(d, i, '(fun x_e => %s x_e)' % t.t)], 'decoy', 'eta'))
                if t.k == 'id' and t.t in ('FILTER', 'EVERY', 'EXISTS', 'LIST_REL', 'OPT_MMAP') and i + 1 < b and T[i + 1].k == 'id' \
                        and T[i + 1].t in self.ops.known:
                    cands.append(Cand(d, 'R4', [self.ops.edit_tok(d, i + 1, '(fun x_e => %s x_e)' % T[i + 1].t)], 'decoy', 'eta'))
                if t.k == 'id' and t.t in ('mem',) and False:
                    pass
        return cands

    # R5: unfold / fold an abbreviation
    def r5(self, d):
        T = d.toks
        cands = []
        bound = {T[i - 1].t for i in range(1, len(T)) if T[i].t == ':' and T[i - 1].k == 'id'}
        bound |= {T[i].t for i in range(len(T)) if i in d.prot and T[i].k == 'id'}
        for (a, b) in d.ranges + ([d.type_range] if d.type_range else []):
            for i in range(a, b):
                t = T[i]
                if t.k != 'id' or not d.mutable(i): continue
                if t.t in bound: continue
                if t.t in self.abbrevs and t.t != d.short:
                    params, body, ad = self.abbrevs[t.t]
                    args = self.ops.atoms_after(d, i, b)
                    if len(params) == 0:
                        cands.append(Cand(d, 'R5', [self.ops.edit_tok(d, i, self.ops.wrap(d, i, i + 1, body))], 'decoy', 'unfold ' + t.t))
                    elif len(args) >= len(params) and all(args[k] for k in range(len(params))):
                        sub = body
                        for k, p in enumerate(params):
                            sub = re.sub(r"(?<![\w'.])" + re.escape(p) + r"(?![\w'])", lambda m, k=k: d.txt(*args[k]) if self.ops.atomic_text(d.txt(*args[k])) else '(' + d.txt(*args[k]) + ')', sub)
                        last = args[len(params) - 1][1]
                        cands.append(Cand(d, 'R5', [(t.s, T[last - 1].e, self.ops.wrap(d, i, last, sub))], 'decoy', 'unfold ' + t.t))
                if t.k == 'id' and t.t in ('strlen', 'explode', 'strsub', 'substring'):
                    args = self.ops.atoms_after(d, i, b)
                    if args and args[0] and args[0][1] - args[0][0] == 1 and T[args[0][0]].k == 'id':
                        a0 = args[0][0]
                        cands.append(Cand(d, 'R5', [(T[a0].s, T[a0].e, '(implode (explode %s))' % T[a0].t)], 'decoy',
                                          'identity round-trip conversion'))
        # fold: replace a parameterless abbreviation body by its name
        for nm, (params, body, ad) in self.abbrevs.items():
            if params or nm == d.short or len(body) < 4: continue
            for (a, b) in d.ranges + ([d.type_range] if d.type_range else []):
                txt_range = d.txt(a, b) if b > a else ''
                for m in re.finditer(re.escape(body), txt_range):
                    s = T[a].s + m.start()
                    cands.append(Cand(d, 'R5', [(s, s + len(body), nm)], 'decoy', 'fold ' + nm))
        return cands

    # R6: equivalent if/match forms
    def r6(self, d):
        T = d.toks
        cands = []
        for (a, b) in d.ranges:
            for i in range(a, b):
                if T[i].k == 'id' and T[i].t == 'if' and d.mutable(i):
                    r = self.ops.if_parts(d, i, b)
                    if not r: continue
                    then_i, else_i, end = r
                    cond = d.txt(i + 1, then_i)
                    if cond.startswith('h :') or ' : ' in cond[:6]:
                        continue
                    tx = d.txt(then_i + 1, else_i)
                    ex = d.txt(else_i + 1, end)
                    if chr(10) in tx or chr(10) in ex: continue
                    cands.append(Cand(d, 'R6', [(T[i].s, T[end - 1].e, 'if ¬ ' + self.ops.neg_wrap(d, i + 1, then_i, cond) + ' then ' +
                                                 self.ops.branch_wrap(ex) + ' else ' + self.ops.branch_wrap(tx))],
                                      'decoy', 'if c a b := if ¬c b a'))
                if T[i].t == '≠' and T[i].k == 'sym' and d.mutable(i):
                    lo, hi = self.span_around(d, i, a, b)
                    if lo is None: continue
                    cands.append(Cand(d, 'R6', [(T[lo[0]].s, T[hi[1] - 1].e, '¬ ' + d.txt(*lo) + ' = ' + d.txt(*hi))],
                                      'decoy', 'a ≠ b := ¬ a = b'))
        # reorder adjacent match arms whose patterns cannot overlap
        if d.kind in ('def', 'abbrev'):
            for arms in d.arm_groups():
                for k in range(len(arms) - 1):
                    A, B = arms[k], arms[k + 1]
                    if not self.ops.arms_disjoint(d, A, B): continue
                    ta = d.txt(A['bar'], A['end']); tb = d.txt(B['bar'], B['end'])
                    sep = d.text[T[A['end'] - 1].e:T[B['bar']].s]
                    cands.append(Cand(d, 'R6', [(T[A['bar']].s, T[B['end'] - 1].e, tb + sep + ta)], 'decoy',
                                      'reorder disjoint arms %d,%d' % (k + 1, k + 2)))
        return cands


# ----------------------------------------------------------------------------------------------
# 5. compile checking
# ----------------------------------------------------------------------------------------------
class Compiler:
    def __init__(self, work, mods, nworkers, log):
        self.work, self.mods, self.n, self.log = work, mods, nworkers, log
        self.S = work + '/stripped'
        rc, so, se = run(['lean', '--print-prefix'], cwd=self.S)     # cwd matters: elan picks the toolchain from lean-toolchain
        self.lean = so.strip().replace(BS, '/') + '/bin/lean.exe'
        self.batt = self.S + '/.lake/packages/batteries/.lake/build/lib/lean'
        self.base_lib = self.S + '/.lake/build/lib/lean'
        self.q = queue.Queue()
        for i in range(nworkers):
            self.setup_worker(i)
            self.q.put(i)
        self.cache_path = work + '/compile_cache2.jsonl'     # append-only: a rerun resumes from it
        self.cache = {}
        old = work + '/compile_cache.jsonl'                   # v1 cache: successes are still valid (same text, same result)
        if os.path.exists(old):
            with open(old, encoding='utf-8') as fh:
                for ln in fh:
                    try:
                        r = json.loads(ln)
                        if r['v'].get('ok'):
                            v = dict(r['v']); v.setdefault('aux_only', False); v.setdefault('err_class', None)
                            self.cache[r['k']] = v
                    except Exception:
                        pass
        if os.path.exists(self.cache_path):
            with open(self.cache_path, encoding='utf-8') as fh:
                for ln in fh:
                    try:
                        r = json.loads(ln)
                        self.cache[r['k']] = r['v']
                    except Exception:
                        pass
        self.lock = threading.Lock()
        self.chains = {}
        self.stats = Counter()

    def setup_worker(self, i):
        w = '%s/w%d' % (self.work, i)
        o = '%s/o%d' % (self.work, i)
        if os.path.isdir(w): shutil.rmtree(w)
        if os.path.isdir(o): shutil.rmtree(o)
        shutil.copytree(self.S + '/CandleLean', w + '/CandleLean')
        shutil.copy2(self.S + '/CandleLean.lean', w + '/CandleLean.lean')
        shutil.copytree(self.base_lib, o)

    def chain(self, module):
        if module not in self.chains:
            self.chains[module] = dependents_chain(self.mods, module)
        return self.chains[module]

    def key(self, module, new_file):
        return hashlib.sha256((module + '\n' + new_file).encode('utf-8')).hexdigest()

    def check(self, module, new_file):
        k = self.key(module, new_file)
        with self.lock:
            if k in self.cache:
                return self.cache[k]
        wi = self.q.get()
        try:
            res = self._compile(wi, module, new_file)
        finally:
            self.q.put(wi)
        with self.lock:
            self.cache[k] = res
            with open(self.cache_path, 'a', encoding='utf-8') as fh:
                fh.write(json.dumps({'k': k, 'v': res}) + chr(10))
        return res

    ERR_RE = re.compile(r"^(CandleLean/[^:]+[.]lean):(\d+):(\d+): error")

    def _run_chain(self, w, o, env, chain):
        for m in chain:
            r = self.mods[m]['rel']
            oo = '%s/%s.olean' % (o, m.replace('.', '/'))
            try:
                rc, so, se = run([self.lean, '-R', '.', '-o', oo, r], cwd=w, env=env, timeout=LEAN_TIMEOUT)
            except subprocess.TimeoutExpired:
                return False, m, [], '', True
            if rc != 0:
                errs = []
                for l in so.splitlines():
                    mm = self.ERR_RE.match(l)
                    if mm:
                        errs.append((int(mm.group(2)), l))
                return False, m, errs, so, False
        return True, None, [], '', False

    def classify(self, m, text, errs, sorried):
        """Where do the errors of module m (compiled from `text`) sit?  Returns (class, lemma decls, names)."""
        ds = split_decls(m, self.mods[m]['path'], text)
        base = {d.full: d.text for d in self.mods[m]['decls']}
        changed = {d.full for d in ds if base.get(d.full) != d.text and (m, d.full) not in sorried}
        classes, lemmas, names = [], [], []
        for (line, msg) in errs:
            hit = None
            for d in ds:
                if d.line <= line <= d.line + d.text.count(chr(10)):
                    hit = d; break
            if hit is None:
                classes.append('other'); names.append('?'); continue
            names.append(hit.full)
            if hit.full in changed:
                classes.append('self')
            elif hit.kind in ('theorem', 'lemma') and not hit.sorry_stmt:
                classes.append('proved_lemma')
                if hit not in lemmas: lemmas.append(hit)
            elif hit.kind in ('theorem', 'lemma'):
                classes.append('statement')
            else:
                classes.append('def')
        if not classes:
            return 'other', [], names
        if 'self' in classes: cls = 'self'
        elif all(c == 'proved_lemma' for c in classes): cls = 'proved_lemma'
        else: cls = 'other_decl'
        return cls, lemmas, names

    def _sorry_decl(self, text, d):
        T = d.toks
        head = d.assign if d.assign is not None else d.arms_start
        if head is None: return text
        new = d.text[:T[head].s] + ':= by sorry'
        return text[:d.start] + new + text[d.start + len(d.text):]

    def _compile(self, wi, module, new_file):
        w = '%s/w%d' % (self.work, wi)
        o = '%s/o%d' % (self.work, wi)
        env = dict(os.environ)
        env['LEAN_PATH'] = o + ';' + self.batt
        chain = self.chain(module)
        t0 = time.time()
        texts = {module: new_file}
        written = set()
        sorried = set()
        res = {'ok': False, 'modules': chain, 'err': '', 'aux_only': False, 'aux_sorried': [], 'err_class': None}
        try:
            for rnd in range(6):
                for m, t in texts.items():
                    with open(w + '/' + self.mods[m]['rel'], 'w', encoding='utf-8', newline='\n') as fh:
                        fh.write(t)
                    written.add(m)
                ok, m, errs, raw, to = self._run_chain(w, o, env, chain)
                if ok:
                    if rnd == 0: res['ok'] = True
                    else:
                        res['aux_only'] = True
                        res['aux_sorried'] = sorted('%s:%s' % x for x in sorried)
                    break
                if to:
                    res['err'] = 'timeout in ' + m; res['err_class'] = 'timeout'; break
                text_m = texts.get(m, self.mods[m]['text'])
                cls, lemmas, names = self.classify(m, text_m, errs, sorried)
                if rnd == 0:
                    first = errs[0][1] if errs else raw[:200]
                    res['err'] = (m + ': ' + first)[:300]
                    res['err_class'] = cls
                    res['err_decls'] = names[:4]
                if cls != 'proved_lemma' or not lemmas:
                    if rnd > 0: res['aux_blocked_by'] = cls
                    break
                # apply all lemma replacements to the (re-parsed) text, last decl first so offsets stay valid
                for d in sorted(lemmas, key=lambda x: -x.start):
                    text_m = self._sorry_decl(text_m, d)
                    sorried.add((m, d.full))
                texts[m] = text_m
        finally:
            for m in written:
                with open(w + '/' + self.mods[m]['rel'], 'w', encoding='utf-8', newline='\n') as fh:
                    fh.write(self.mods[m]['text'])
            for m in chain:
                src = '%s/%s.olean' % (self.base_lib, m.replace('.', '/'))
                dst = '%s/%s.olean' % (o, m.replace('.', '/'))
                shutil.copy2(src, dst)
        res['secs'] = round(time.time() - t0, 1)
        return res

    def save(self):
        pass


# ----------------------------------------------------------------------------------------------
# 6. enumeration, dedupe, seed order
# ----------------------------------------------------------------------------------------------
def sha(s):
    return hashlib.sha256(s.encode('utf-8')).hexdigest()


def scope_of(d):
    if d.module.startswith('CandleLean.Prelude.'):
        return 'prelude'
    if d.kind in ('theorem', 'lemma'):
        return 'statement'
    return 'definition'


def finalize(c):
    d = c.decl
    new_decl = apply_edits(d.text, c.edits)
    c.new_decl = new_decl
    m = d.module
    # full new file text
    ftxt = None
    c.scope = scope_of(d)
    c.label = 'V-C' if c.op == 'U1' else 'V-P'
    c.key = '%s|%s|%s|%s' % (d.module, d.full, c.op, sha(new_decl)[:12])
    c.rank = sha('%d:%s' % (SEED, c.key))
    lo = min(e[0] for e in c.edits); hi = max(e[1] for e in c.edits)
    c.old_span = d.text[lo:hi]
    new_hi = hi + (len(new_decl) - len(d.text))
    c.new_span = new_decl[lo:new_hi]
    return c



def paren_fingerprint(text):
    """number of redundant parenthesis groups: (x) around one token, or ((...)) / ([...]) around one bracket group."""
    T = tokenize(text)
    stack, match = [], {}
    for i, t in enumerate(T):
        if t.k == 'sym' and t.t in OPEN:
            stack.append(i)
        elif t.k == 'sym' and t.t in CLOSE and stack:
            j = stack.pop(); match[j] = i; match[i] = j
    n = 0
    for i, t in enumerate(T):
        if t.k == 'sym' and t.t == '(' and i in match:
            j = match[i]
            if j == i + 2:
                n += 1
            elif i + 1 < len(T) and T[i + 1].t in OPEN and match.get(i + 1) == j - 1:
                n += 1
    return n


def enumerate_all(mods, opsobj, decoyobj, log):
    mut, dec = [], []
    elig = defaultdict(set)         # op -> declarations to which the operator is applicable at all
    for mname in sorted(mods):
        for d in mods[mname]['decls']:
            if d.name is None or d.name.startswith('Aux.'):
                continue
            for c in opsobj.all_for(d):
                mut.append(c)
            for c in decoyobj.all_for(d):
                dec.append(c)
    def dedupe(lst):
        seen, out = set(), []
        lst = sorted(lst, key=lambda c: 0 if c.op in ('N4', 'H3', 'U1') else 1)   # specific operators win ties
        for c in lst:
            finalize(c)
            if c.new_decl == c.decl.text:
                continue                                  # eligibility 2: byte-identical to base
            FP_STATS['seen'] += 1
            if paren_fingerprint(c.new_decl) > paren_fingerprint(c.decl.text):
                FP_STATS['dropped'] += 1
                FP_STATS['by_op'][c.op] += 1
                continue                                  # would show a redundant parenthesis the base text lacks
            k = (c.decl.module, c.decl.full, sha(c.new_decl))
            if k in seen:
                continue                                  # eligibility 3: same change at the same declaration
            seen.add(k)
            out.append(c)
        out.sort(key=lambda c: c.rank)
        for i, c in enumerate(out):
            c.pos = i
        return out
    FP_STATS['seen'] = FP_STATS['dropped'] = 0
    FP_STATS['by_op'] = Counter()
    m_out = dedupe(mut)
    FP_STATS['mut'] = {'seen': FP_STATS['seen'], 'dropped': FP_STATS['dropped'], 'by_op': dict(FP_STATS['by_op'])}
    FP_STATS['seen'] = FP_STATS['dropped'] = 0
    FP_STATS['by_op'] = Counter()
    d_out = dedupe(dec)
    FP_STATS['dec'] = {'seen': FP_STATS['seen'], 'dropped': FP_STATS['dropped'], 'by_op': dict(FP_STATS['by_op'])}
    return m_out, d_out


def mutated_file(mods, c):
    m = mods[c.decl.module]
    t = m['text']
    s = c.decl.start
    return t[:s] + c.new_decl + t[s + len(c.decl.text):]


# applicability of each operator (eligible declaration classes) for the "unreached sites" count
def applicable(op, d):
    k = d.kind
    if d.name is None or d.name.startswith('Aux.'): return False
    if k in ('theorem', 'lemma') and not d.sorry_stmt: return False
    if op in ('W1', 'W2', 'W3', 'W4', 'H1', 'H2', 'H3'):
        return (k in ('theorem',) and d.sorry_stmt) or (k in ('def', 'abbrev') and d.prop_valued) or (k == 'inductive' and d.prop_valued)
    if op == 'U1':
        return k == 'opaque' or (k in ('def', 'abbrev') and '@Classical.epsilon' in d.text)
    if op in ('D1', 'D2', 'D3', 'D4', 'N4'):
        return k in ('def', 'abbrev') and (op != 'D3' or True)
    if op == 'T1':
        return k in ('def', 'abbrev', 'theorem', 'inductive')
    if op.startswith('R'):
        return k in ('def', 'abbrev', 'theorem', 'inductive')
    return k in ('def', 'abbrev', 'theorem', 'inductive')


# ----------------------------------------------------------------------------------------------
# 7. sampling
# ----------------------------------------------------------------------------------------------
def accepted(r):
    return bool(r) and (r.get('ok') or (SORRY_AUX and r.get('aux_only')))


class Sampler:
    def __init__(self, mods, comp, cands, log, scope_quota, target, groupfn, group_min, group_order, max_per_decl=MAX_PER_DECL):
        self.mods, self.comp, self.cands, self.log = mods, comp, cands, log
        self.quota = dict(scope_quota)
        self.cap = MAX_OP_SHARE
        self.target = target
        self.groupfn, self.group_min, self.group_order = groupfn, group_min, group_order
        self.chosen, self.per_decl, self.per_scope = [], Counter(), Counter()
        self.attempted = {}       # cand.key -> result
        self.max_per_decl = max_per_decl
        self.per_op = Counter()

    def ensure(self, window):
        todo = [c for c in window if c.key not in self.attempted]
        if not todo: return
        def job(c):
            return c, self.comp.check(c.decl.module, mutated_file(self.mods, c))
        with ThreadPoolExecutor(max_workers=self.comp.n) as ex:
            for c, r in ex.map(job, todo):
                self.attempted[c.key] = r
        self.comp.save()

    def can_take(self, c):
        if any(c is x for x in self.chosen): return False
        if self.per_decl[(c.decl.module, c.decl.full)] >= self.max_per_decl: return False
        if self.per_scope[c.scope] >= self.quota.get(c.scope, 10 ** 9): return False
        if self.cap is not None and self.per_op[c.op] >= max(1, int(self.cap * self.target)): return False
        return True

    def take(self, c):
        self.chosen.append(c)
        self.per_decl[(c.decl.module, c.decl.full)] += 1
        self.per_scope[c.scope] += 1
        self.per_op[c.op] += 1

    def run_group(self, g, need, W=36):
        lst = [c for c in self.cands if self.groupfn(c) == g]
        have = sum(1 for c in self.chosen if self.groupfn(c) == g)
        i = 0
        while have < need and i < len(lst):
            window = [c for c in lst[i:i + W] if self.can_take(c)]
            self.ensure(window)
            for c in lst[i:i + W]:
                if have >= need: break
                if self.can_take(c) and accepted(self.attempted.get(c.key)):
                    self.take(c); have += 1
            i += W
        return have

    def fill(self, W=36):
        i = 0
        total = lambda: len(self.chosen)
        while total() < self.target and i < len(self.cands):
            window = [c for c in self.cands[i:i + W] if self.can_take(c)]
            self.ensure(window)
            for c in self.cands[i:i + W]:
                if total() >= self.target: break
                if self.can_take(c) and accepted(self.attempted.get(c.key)):
                    self.take(c)
            i += W
        return i

    def run(self):
        for g in self.group_order:
            self.run_group(g, self.group_min(g))
        self.fill()


# ----------------------------------------------------------------------------------------------
# 8. output
# ----------------------------------------------------------------------------------------------
def unified(c):
    a = c.decl.text.split('\n'); b = c.new_decl.split('\n')
    rel = c.decl.module.replace('.', '/') + '.lean'
    return '\n'.join(difflib.unified_diff(a, b, 'a/' + rel, 'b/' + rel, lineterm='', n=2))


def record(c, idx, prefix, attempt):
    d = c.decl
    r = {
        'id': '%s-%04d' % (prefix, idx),
        'cand_key': c.key,
        'family': c.family,
        'operator': c.op,
        'scope': c.scope,
        'module': d.module,
        'file': d.module.replace('.', '/') + '.lean',
        'declaration': d.full,
        'kind': d.kind,
        'line': d.line,
        'label': c.label,
        'tag': c.tag,
        'tag_provisional': True,
        'seed': SEED,
        'seed_position': c.pos,
        'note': c.note,
        'old_text': c.old_span,
        'new_text': c.new_span,
        'old_decl': d.text,
        'new_decl': c.new_decl,
        'diff': unified(c),
        'compile': {'status': 'ok' if attempt.get('ok') else ('ok_aux_sorried' if attempt.get('aux_only') else 'fail'), 'aux_sorried': attempt.get('aux_sorried') or [], 'checked_modules': attempt.get('modules'),
                    'check': 'lean elaboration of the mutated module and all its dependents (sorry allowed)'},
    }
    if prefix == 'DEC':
        r['label'] = 'decoy'
        r['tag'] = 'decoy'
        r['equivalence_proof'] = None
    return r


INTERP = [
    'Scope: `prelude` = modules under `CandleLean/Prelude/`; `statement` = theorem statements whose proof is exactly `by sorry` (never `Aux.*`, never proved theorems); `definition` = every other def, abbrev, opaque, inductive outside the prelude (Misc, Mllist, Mlstring, SetSpec, HolSyntax*, HolSemantics*).',
    'Label: V-C for U1 (unspecified values), V-P for every other operator. Provisional silent/visible: silent for U1, W2, and for W1, W3, W4, H1, H2 only where the polarity of the position makes the change a weakening; everything else visible. Polarity comes from a small implication/negation walk, not from Lean.',
    'Eligibility 1 is Lean elaboration of the mutated module and all modules that import it, other proofs unchanged: a definition mutant that breaks a proved lemma depending on it fails and is not sampled. Compilation runs `lean -o` per module against a per-worker copy of the stripped build (what `lake build` runs, without touching .lake state); `lake build` itself was used for the stripped-copy check.',
    'Eligibility 3 is applied across operators: two candidates giving the same new declaration text are one candidate; the more specific operator (N4, H3, U1) wins the tie.',
    'Sampling: pool target 180 (60/25/15 percent by scope), at most 2 per declaration; first the family minimum (6, and 5 per held-out operator) is filled in seed order, then the rest in seed order. No operator may exceed 12 percent of the pool (`--max-op-share`, 0 disables). Nothing is relaxed silently: a scope, family, held-out or pool-size quota that cannot be met is listed under `unmet_quotas` in `stats.json` and below.',
    'U1 is reached by: `opaque` to `def` for a package whose witness is an explicit function (exposes the fixed unspecified case), the same with the fallback constant changed, an opaque constant defined as `ARB`, and a Hilbert-choice definition replaced by its witness. Packages whose witness is `Classical.choose _exists` have no value to expose and are skipped (unreached).',
    'O1: this base has no union/intersection or set-image overloads (no union or intersection tokens), so the swaps used are the pairs in `O1_PAIRS` in `gen.py`. C3 only drops a conversion (an added `implode (explode x)` round trip is an identity, so it is a decoy, not a mutant).',
    'D4 as a mutant: reorder two adjacent arms only if their patterns can overlap, or remove an arm that a later total arm covers. Reordering arms with disjoint patterns is equivalent and is the decoy R6 (arm reorder).',
    'T1 only changes the type of a binder whose variable the body uses, to a type that is not convertible to the old one (no Int to Nat).',
    'Redundant parentheses: mutated text keeps only parentheses Lean needs. A candidate whose new declaration has more redundant `(x)` or `((...))` groups than the base declaration is dropped; the pool and decoy shares are in `stats.json` under `paren_fingerprint`.',
    'Eligibility-1 bias: a definition mutant is rejected if any proved auxiliary lemma in the base stops compiling. A first-N sample in seed order measures how many candidates fail only for that reason (`eligibility1_bias` in `stats.json`). Option `--sorry-aux` accepts such candidates, rebuilding with the broken proved lemmas restated as `:= by sorry`; it is off by default (SPEC rule) and the records then carry `compile.status = ok_aux_sorried` and the list of restated lemmas.',
    'H1 and W1-W4 act on theorem statements, Prop-valued definitions and inductive Prop constructors; H3 moves a quantifier across a conjunct only where the variable also occurs in a sibling conjunct.',
    'Decoys come from R1-R6 on definitions, Prop inductives and sorry statements; here they are only compile-checked, not shown equivalent.',
]


def write_readme(out, stats, pool, S):
    L = []
    A = L.append
    A('# Mutant and decoy generator (audit experiment)')
    A('')
    A('Generated by `gen.py` (seed %d). Rerun it instead of editing by hand.' % stats['seed'])
    A('')
    A('## Files')
    A('- `gen.py`: the generator (strip, enumerate, compile-check, sample, write).')
    A('- `pool.jsonl`: sampled mutants, one JSON record per line (all compile).')
    A('- `decoys.jsonl`: sampled decoys (meaning-preserving rewrites; compile only; `equivalence_proof` is null).')
    A('- `stats.json`: numbers behind the tables below. `gen.log`: run log.')
    A('- Work area, not a deliverable: `E:/ts_ws/mut_work` (comment-stripped copy `stripped/`, per-worker scratch `w0..w5`, `o0..o5`, append-only `compile_cache2.jsonl`).')
    A('')
    A('## Record fields')
    A('`id`, `family`, `operator`, `scope` (definition, prelude, statement), `module`, `file`, `declaration`, `kind`, `line` (in the comment-stripped file), '
      '`label` (V-C for U1, V-P otherwise), `tag` (silent or visible) with `tag_provisional: true`, `seed`, `seed_position`, `note`, '
      '`old_text` and `new_text` (the changed span), `old_decl` and `new_decl` (whole declaration), `diff` (unified), `compile` (status, modules checked, aux_sorried).')
    A('')
    A('## How to rerun')
    A('```')
    A('python gen.py all     # strip + build the stripped copy, enumerate, compile, sample, write')
    A('python gen.py run     # same without re-stripping; resumes from compile_cache2.jsonl')
    A('python gen.py run --sorry-aux   # option: accept mutants whose only failure is a proved aux lemma, restated as sorry (off by default)')
    A('python gen.py enum    # enumeration only (no compile)')
    A('```')
    A('Needs Lean 4.28.0 (elan) and lake on PATH, and `PYTHONUTF8=1` on Windows. Paths are constants at the top of `gen.py` (BASE, WORK, OUT); the base is only read. '
      'Compile results are appended to `compile_cache2.jsonl` as they finish, so an interrupted run resumes without recompiling. '
      'The pool does not depend on the cache or on thread timing: candidates are ordered by SHA-256 of `seed:candidate-key` and selection walks that order.')
    A('')
    A('## Per-operator table (mutants)')
    A('`eligible`: declarations of a kind the operator can apply to; `reached`: with at least one candidate; `unreached`: skipped, no scripted way in; `cands`: distinct candidates after eligibility 2-3; '
      '`attempted`: compile-checked (lazily, in seed order, until the quotas were met); `compiled`: elaborate; `sampled`: in `pool.jsonl`.')
    A('')
    A('| op | family | eligible | reached | unreached | cands | attempted | compiled | sampled |')
    A('|---|---|---|---|---|---|---|---|---|')
    for op, v in stats['ops'].items():
        A('| %s | %s | %d | %d | %d | %d | %d | %d | %d |' % (op, v['family'], v['eligible_decls'], v['sites_reached'], v['unreached'],
                                                          v['candidates'], v['attempted'], v['compiled'], v['sampled']))
    A('')
    A('Pool size %d; per scope %s (quota %s).' % (stats['pool_size'], stats['per_scope'], stats['scope_quota']))
    A('')
    A('Per family (minimum %d, held-out operators %d):' % (MIN_PER_FAMILY, MIN_PER_HELD))
    A('')
    A('| family | sampled | silent (provisional) | visible |')
    A('|---|---|---|---|')
    fams = FAMILY_ORDER + HELD
    for f in fams:
        rows = [c for c in pool if (c.op if f in HELD else c.family) == f]
        A('| %s | %d | %d | %d |' % (f, len(rows), sum(1 for c in rows if c.tag == 'silent'),
                                   sum(1 for c in rows if c.tag == 'visible')))
    A('')
    A('Unmet quotas: %s' % (stats.get('unmet_quotas') or 'none'))
    A('Largest operator share of the pool: %s (cap %s).' % (stats.get('op_share_max'), stats.get('max_op_share')))
    b = stats.get('eligibility1_bias') or {}
    if b:
        A('')
        A('Eligibility-1 bias (first %d candidates in seed order of %d enumerated): classes %s; share failing only because a proved aux lemma broke: %s of the sample (extrapolated %s candidates).' % (
            b['sample_size'], b['enumerated'], b['classes'], b['aux_only_share_of_sample'], b['aux_only_extrapolated']))
    A('Redundant-paren share (new text with more redundant parens than base): %s.' % stats.get('paren_fingerprint'))
    A('')
    A('## Per-operator table (decoys)')
    A('| op | cands | attempted | compiled | sampled |')
    A('|---|---|---|---|---|')
    for op, v in stats.get('decoys', {}).items():
        A('| %s | %d | %d | %d | %d |' % (op, v['candidates'], v['attempted'], v['compiled'], v['sampled']))
    A('')
    A('## Interpretations of SPEC')
    for t in INTERP:
        A('- ' + t)
    A('')
    with open(out + '/README.md', 'w', encoding='utf-8', newline=chr(10)) as fh:
        fh.write(chr(10).join(L) + chr(10))


def main():
    global MAX_OP_SHARE, SORRY_AUX
    ap = argparse.ArgumentParser()
    ap.add_argument('stage', nargs='?', default='all', choices=['all', 'strip', 'enum', 'run'])
    ap.add_argument('--work', default=WORK)
    ap.add_argument('--out', default=OUT)
    ap.add_argument('--workers', type=int, default=NWORK)
    ap.add_argument('--no-decoys', action='store_true')
    ap.add_argument('--max-op-share', type=float, default=MAX_OP_SHARE, help='cap on one operator share of the pool; 0 disables')
    ap.add_argument('--sorry-aux', action='store_true', help='accept mutants whose only failures are proved lemmas (restated as sorry); off = SPEC rule')
    ap.add_argument('--bias-sample', type=int, default=BIAS_SAMPLE)
    ap.add_argument('--pool', type=int, default=POOL_TARGET)
    args = ap.parse_args()
    MAX_OP_SHARE = args.max_op_share or None
    SORRY_AUX = args.sorry_aux
    work, out = args.work, args.out
    logf = open(out + '/gen.log', 'a', encoding='utf-8')
    def log(s):
        line = time.strftime('%H:%M:%S ') + s
        print(line, flush=True)
        logf.write(line + '\n'); logf.flush()
    t0 = time.time()
    info = {}
    if args.stage in ('all', 'strip'):
        info['strip'] = stage_strip(work, log)
        with open(work + '/strip_info.json', 'w') as fh: json.dump(info['strip'], fh)
        if args.stage == 'strip': return
    elif os.path.exists(work + '/strip_info.json'):
        info['strip'] = json.load(open(work + '/strip_info.json'))
    mods = load_modules(work + '/stripped')
    ndecl = sum(len(m['decls']) for m in mods.values())
    log('parsed %d modules, %d declarations' % (len(mods), ndecl))
    opsobj = Ops(mods)
    decoyobj = DecoyOps(opsobj)
    mut, dec = enumerate_all(mods, opsobj, decoyobj, log)
    log('enumerated %d mutant candidates and %d decoy candidates (after eligibility 2-3 and the paren filter)' % (len(mut), len(dec)))
    log('paren filter: mutants %s ; decoys %s' % (FP_STATS['mut'], FP_STATS['dec']))
    cnt = Counter(c.op for c in mut)
    log('mutant candidates per operator: ' + ', '.join('%s=%d' % (k, cnt[k]) for k in sorted(cnt)))
    cnt = Counter(c.op for c in dec)
    log('decoy candidates per operator: ' + ', '.join('%s=%d' % (k, cnt[k]) for k in sorted(cnt)))
    if args.stage == 'enum':
        return mods, opsobj, decoyobj, mut, dec
    comp = Compiler(work, mods, args.workers, log)
    # ---- mutants
    quota = {s: int(round(args.pool * v)) for s, v in SCOPE_SHARE.items()}
    def gfn(c):
        return c.op if c.op in HELD else c.family
    def gmin(g):
        return MIN_PER_HELD if g in HELD else MIN_PER_FAMILY
    order = FAMILY_ORDER + HELD
    S = Sampler(mods, comp, mut, log, quota, args.pool, gfn, gmin, order)
    S.run()
    log('mutant pool: %d chosen; per scope %s' % (len(S.chosen), dict(S.per_scope)))
    pool = sorted(S.chosen, key=lambda c: c.pos)
    with open(out + '/pool.jsonl', 'w', encoding='utf-8', newline='\n') as fh:
        for i, c in enumerate(pool, 1):
            fh.write(json.dumps(record(c, i, 'MUT', S.attempted[c.key]), ensure_ascii=False) + '\n')
    # ---- decoys
    D = None
    if not args.no_decoys:
        dq = {s: 10 ** 9 for s in SCOPE_SHARE}
        D = Sampler(mods, comp, dec, log, dq, DECOY_TARGET, lambda c: c.op, lambda g: DECOY_MIN_PER_OP, DECOY_OPS)
        D.cap = None
        D.run()
        log('decoy pool: %d chosen' % len(D.chosen))
        dpool = sorted(D.chosen, key=lambda c: c.pos)
        with open(out + '/decoys.jsonl', 'w', encoding='utf-8', newline='\n') as fh:
            for i, c in enumerate(dpool, 1):
                fh.write(json.dumps(record(c, i, 'DEC', D.attempted[c.key]), ensure_ascii=False) + '\n')
    # ---- eligibility-1 bias: compile the first N candidates in seed order (a random sample of the enumerated set)
    bias = {}
    nb = min(args.bias_sample, len(mut))
    if nb:
        sample = mut[:nb]
        for i in range(0, nb, 120):
            S.ensure(sample[i:i + 120])
        cls = Counter()
        by_scope = defaultdict(Counter)
        for c in sample:
            r = S.attempted[c.key]
            k = 'ok' if r.get('ok') else ('aux_only' if r.get('aux_only') else 'fail_' + str(r.get('err_class')))
            cls[k] += 1
            by_scope[c.scope][k] += 1
        bias = {'sample_size': nb, 'enumerated': len(mut), 'classes': dict(cls),
                'by_scope': {k: dict(v) for k, v in by_scope.items()},
                'aux_only_share_of_sample': round(cls['aux_only'] / nb, 4),
                'aux_only_share_of_failures': round(cls['aux_only'] / max(1, nb - cls['ok']), 4),
                'aux_only_extrapolated': int(round(cls['aux_only'] / nb * len(mut)))}
        log('eligibility-1 bias sample: %s' % bias)
    # ---- parenthesis fingerprint of the final pools
    def newparen(c):
        return paren_fingerprint(c.new_decl) > paren_fingerprint(c.decl.text)
    fp = {'mutants_pool': round(sum(1 for c in pool if newparen(c)) / max(1, len(pool)), 4),
          'enumerated_before_filter': {k: v for k, v in FP_STATS.items() if k in ('mut', 'dec')}}
    if D is not None:
        fp['decoys_pool'] = round(sum(1 for c in dpool if newparen(c)) / max(1, len(dpool)), 4)
    log('redundant-paren share (new text has more redundant parens than base): %s' % fp)
    comp.save()
    # ---- statistics
    stats = {'seed': SEED, 'pool_target': args.pool, 'scope_quota': quota, 'ops': {}, 'families': {}}
    all_ops = list(FAMILY.keys())
    for op in all_ops:
        eligd = {(d.module, d.full) for m in mods.values() for d in m['decls'] if applicable(op, d)}
        reached = {(c.decl.module, c.decl.full) for c in mut if c.op == op}
        att = [c for c in mut if c.op == op and c.key in S.attempted]
        stats['ops'][op] = {
            'family': FAMILY[op],
            'eligible_decls': len(eligd), 'sites_reached': len(reached), 'unreached': len(eligd - reached),
            'candidates': sum(1 for c in mut if c.op == op), 'attempted': len(att),
            'compiled': sum(1 for c in att if accepted(S.attempted[c.key])),
            'sampled': sum(1 for c in S.chosen if c.op == op)}
    dstats = {}
    if D is not None:
        for op in DECOY_OPS:
            att = [c for c in dec if c.op == op and c.key in D.attempted]
            dstats[op] = {'candidates': sum(1 for c in dec if c.op == op), 'attempted': len(att),
                          'compiled': sum(1 for c in att if accepted(D.attempted[c.key])),
                          'sampled': sum(1 for c in D.chosen if c.op == op)}
    stats['decoys'] = dstats
    stats['pool_size'] = len(S.chosen)
    stats['per_scope'] = dict(S.per_scope)
    stats['strip'] = info.get('strip')
    stats['eligibility1_bias'] = bias
    stats['paren_fingerprint'] = fp
    stats['max_op_share'] = MAX_OP_SHARE
    stats['sorry_aux'] = SORRY_AUX
    unmet = []
    for sc, q in quota.items():
        if S.per_scope[sc] < q: unmet.append('scope %s: %d of %d' % (sc, S.per_scope[sc], q))
    for g in FAMILY_ORDER + HELD:
        have = sum(1 for c in S.chosen if gfn(c) == g)
        need = MIN_PER_HELD if g in HELD else MIN_PER_FAMILY
        if have < need: unmet.append('%s: %d of %d' % (g, have, need))
    if len(S.chosen) < 150: unmet.append('pool %d < 150' % len(S.chosen))
    stats['unmet_quotas'] = unmet
    stats['op_share_max'] = round(max(S.per_op.values()) / max(1, len(S.chosen)), 3)
    log('unmet quotas: %s' % unmet)
    stats['seconds'] = round(time.time() - t0)
    with open(out + '/stats.json', 'w', encoding='utf-8') as fh:
        json.dump(stats, fh, indent=1, ensure_ascii=False)
    write_readme(out, stats, pool, S)
    log('done in %ds' % (time.time() - t0))


if __name__ == '__main__':
    main()
