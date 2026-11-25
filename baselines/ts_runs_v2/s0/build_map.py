#!/usr/bin/env python3
"""Build map_<run>.v0.tsv for the CakeML type-soundness translations from
   (a) the HOL4 constants/types of the export (statements.jsonl),
   (b) the CONVENTIONS.md of the run (tables encoded below; section references in the notes),
   (c) existence checks of the resulting Lean names in the Lean dump (names only; no statement is looked at).
Rows whose Lean name is not stated in CONVENTIONS but found by looking at the Lean environment get status `lookup`.
usage: build_map.py RUN OUTFILE [LEAN_DUMP]
"""
import json, sys

HOL = 'E:/NUS/mcomp/Dissertation/candle_study/tools/hol4_query/out_ts/statements.jsonl'
run, outp = sys.argv[1], sys.argv[2]
dumpf = sys.argv[3] if len(sys.argv) > 3 else 'E:/ts_ws/s0/out/%s/lean_dump0.txt' % run

rows = [json.loads(l) for l in open(HOL, encoding='utf-8') if l.strip()]
consts, types = {}, set()


def wt(t):
    if 'tv' in t:
        return
    types.add(t['ty'])
    for a in t['args']:
        wt(a)


def w(t):
    if 'v' in t:
        wt(t['t'])
    elif 'c' in t:
        consts.setdefault(t['c'], t['t'])
        wt(t['t'])
    elif 'f' in t:
        w(t['f'])
        w(t['x'])
    else:
        wt(t['abs']['t'])
        w(t['body'])


for r in rows:
    for h in r['hyps']:
        w(h)
    w(r['concl'])

defs = {}
for l in open(dumpf, encoding='utf-8'):
    if l.startswith('@@D '):
        d = json.loads(l[4:])
        defs[d['name']] = d

OPUS = run.startswith('opus')
NS = 'CmlTS.' if OPUS else ''
LESS = run == 'opus_lessons'
NOLESS = run == 'opus_nolessons'
SON = run == 'sonnet_lessons'


def res(t):
    while 'ty' in t and t['ty'] == 'min$fun':
        t = t['args'][1]
    return t


# ---------------------------------------------------------------- TYPE rows
tyname = {
    'semanticPrimitives$v': 'value' if LESS else 'val' if NOLESS else 'Value',
    'typeSystem$t': 'Ty' if SON else 'typ',
    'namespace$id': 'Ident' if SON else 'ident',
    'finite_map$fmap': 'FMap' if SON else 'fmap',
    'ast$thunk_op': 'thunk_op_t' if LESS else 'thunk_op',
}
coretypes = {
    'min$bool': ('Prop,Bool', 'convention', 'bool is Prop (predicate results, sonnet: always) or Bool (data, opus runs)'),
    'min$fun': ('@fun', 'lean-core', 'non-dependent pi'),
    'num$num': ('Nat', 'convention', 'num is Nat'),
    'integer$int': ('Int', 'convention', 'int is Int'),
    'list$list': ('List', 'convention', 'list is List'),
    'pair$prod': ('Prod', 'convention', 'pair type'),
    'option$option': ('Option', 'convention', 'option type'),
    'sum$sum': ('Sum', 'convention', 'sum type'),
    'one$one': ('Unit', 'convention', 'unit'),
    'fcp$cart': ('BitVec', 'convention', 'HOL4 word type: (bool, N) cart is BitVec n, width decoded from the bit0/bit1 numeral type'),
}
type_rows = []
for t in sorted(types):
    if t in ('fcp$bit0', 'fcp$bit1'):
        continue
    if t in coretypes:
        l, st, note = coretypes[t]
        type_rows.append(('TYPE', t, l, '', st, note))
        continue
    nm = t.split('$', 1)[1]
    ln = tyname.get(t, nm)
    type_rows.append(('TYPE', t, NS + ln, '', 'convention', 'type name: same name or the CONVENTIONS rename'))
tmap = {r[1]: r[2] for r in type_rows}

# ---------------------------------------------------------------- CONST rows
core = {}


def C(hol, lean, perm='', status='lean-core', note=''):
    core[hol] = (lean, perm, status, note)


C('arithmetic$+', 'HAdd.hAdd')
C('arithmetic$<=', 'LE.le')
C('arithmetic$>=', 'GE.ge')
C('arithmetic$>', 'GT.gt')
C('prim_rec$<', 'LT.lt')
C('integer$int_le', 'LE.le#Int.instLEInt')
C('integer$int_lt', 'LT.lt#Int.instLTInt')
for h in ('arithmetic$BIT1', 'arithmetic$NUMERAL', 'arithmetic$ZERO', 'num$0'):
    C(h, '@num', '', 'convention', 'rule NUM: numeral literal')
C('bool$!', '@forall', '', 'lean-core', 'binder')
C('bool$?', 'Exists')
C('bool$/\\', 'And')
C('bool$\\/', 'Or')
C('bool$~', 'Not,Ne')
C('bool$T', 'True,Bool.true')
C('bool$F', 'False,Bool.false')
C('bool$COND', 'ite')
C('min$=', 'Eq,Iff')
C('min$==>', '@imp')
C('bool$IN', 'Membership.mem', '1,0', 'lean-core', 'Lean mem takes the collection first; list membership is rule LMEM')
C('combin$o', 'Function.comp')
C('list$APPEND', 'HAppend.hAppend,List.append')
C('list$CONS', 'List.cons')
C('list$NIL', 'List.nil')
C('option$NONE', 'Option.none')
C('option$SOME', 'Option.some')
C('pair$,', 'Prod.mk')
C('pair$FST', 'Prod.fst' + (',FST' if SON else ''))
C('pair$SND', 'Prod.snd' + (',SND' if SON else ''))
C('pair$UNCURRY', '@match', '', 'convention', 'rule UNCURRY: lambda over a pair is a one-alternative matcher')
C('relation$RTC', NS + 'RTC', '', 'convention', 'RTC R is RTC R')
C('words$n2w', NS + 'n2w', '', 'convention', 'n2w')
C('integer$Num', NS + 'Num', '', 'convention', 'Num')
C('integer$int_of_num', 'Nat.cast' if NOLESS else NS + 'int_of_num', '', 'convention', '&n is int_of_num n (= (n : Int))')
C('integer$ABS', NS + ('ABS' if (NOLESS or SON) else 'INT_ABS'), '', 'convention', 'ABS on int')
C('combin$I', 'id' if SON else NS + 'I', '', 'convention', 'I (sonnet: id)')
C('combin$K', '@K' if SON else NS + 'K', '', 'convention', 'K (sonnet has no K: the lambda fun _ => x)')
C('bool$ARB', NS + 'ARB', '', 'convention', 'ARB')
if SON:
    for h, n in [('list$LENGTH', 'LENGTH'), ('list$MAP', 'MAP'), ('list$REVERSE', 'REVERSE'), ('list$DROP', 'DROP'),
                 ('list$FOLDR', 'FOLDR'), ('list$ZIP', 'ZIP'), ('rich_list$REPLICATE', 'REPLICATE')]:
        C(h, n, '', 'convention', 'own definition with the HOL4 name in the root namespace (Prelude.List)')
else:
    C('list$LENGTH', 'List.length', '', 'convention', 'LENGTH l is l.length')
    C('list$MAP', 'List.map', '', 'convention', 'MAP f l is l.map f')
    C('list$REVERSE', 'List.reverse', '', 'convention', 'REVERSE l is l.reverse')
    C('list$DROP', 'List.drop', '', 'convention', 'DROP n l is l.drop n; List.drop n l as elaborated')
    C('list$FOLDR', 'List.foldr', '', 'convention', 'FOLDR f e l is List.foldr f e l')
    C('list$ZIP', 'List.zip', '', 'convention', 'ZIP (a,b) is List.zip a b (rule ZIPPAIR)')
    C('rich_list$REPLICATE', 'List.replicate', '', 'convention', 'REPLICATE n x is List.replicate n x')
for h, inst, own in [('pred_set$UNION', 'Union.union', 'UNION'), ('pred_set$INTER', 'Inter.inter', 'INTER'),
                     ('pred_set$DIFF', 'SDiff.sdiff', 'DIFF'), ('pred_set$SUBSET', 'HasSubset.Subset', 'SUBSET'),
                     ('pred_set$INSERT', 'Insert.insert', 'INSERT'),
                     ('pred_set$EMPTY', 'EmptyCollection.emptyCollection', 'EMPTY')]:
    C(h, inst + (',' + NS + own if (NS + own) in defs else ''), '', 'convention', 'set operation: notation instance (and the own name where the run defines it)')

over = {}


def O(hol, lean, note, perm='', status='convention'):
    over[hol] = (lean, perm, status, note)


if LESS:
    O('sptree$domain', 'CmlTS.domain', 'sptree domain keeps its name (Prelude/Sptree)')
    O('sptree$toList', 'CmlTS.spt_toList', 'section 3: sptree$toList is spt_toList')
    O('semanticPrimitives$thunk_op', 'CmlTS.thunk_op', 'section 3: the constant thunk_op keeps its name')
    O('list$isPREFIX', 'CmlTS.isPREFIX', 'a <<= b is isPREFIX a b')
if NOLESS:
    O('sptree$domain', 'CmlTS.domain', 'sptree: domain')
    O('sptree$toList', 'CmlTS.toList', 'sptree: toList (llist toList is llist_toList)')
    O('semanticPrimitives$thunk_op', 'CmlTS.do_thunk_op', 'section 4: thunk_op (function) is do_thunk_op')
    O('list$isPREFIX', 'List.IsPrefix', 'section 3: isPREFIX a b is a <+: b')
    O('list$TL', 'List.tail', 'section 3: TL l is l.tail')
    O('list$LUPDATE', 'List.set', 'section 3: LUPDATE e n l is l.set n e', perm='2,1,0')
    O('finite_map$FLOOKUP', 'CmlTS.fmap.FLOOKUP', 'section 7: fmap is a structure whose field is FLOOKUP')
if SON:
    O('sptree$domain', 'sptree.domain', 'section 3: sptree$domain is sptree.domain')
    O('sptree$toList', 'sptree.toList', 'section 3: sptree$toList is sptree.toList')
    O('semanticPrimitives$thunk_op', "thunk_op'", "section 3: the function thunk_op is thunk_op'")
    O('list$isPREFIX', 'isPREFIX', 'x <<= y is isPREFIX x y')


def ctor_candidates(hol, ty):
    nm = hol.split('$', 1)[1]
    r = res(ty)
    if 'ty' in r and r['ty'] in tmap and not r['ty'].startswith('min$'):
        return [tmap[r['ty']] + '.' + nm]
    return []


def known_core(n):
    base = n.split('#')[0]
    return base in defs or base.split('.')[0] in (
        'HAdd', 'LE', 'LT', 'GE', 'GT', 'Eq', 'And', 'Or', 'Not', 'Ne', 'True', 'False', 'Bool', 'ite', 'Exists', 'Iff',
        'Option', 'Prod', 'List', 'Nat', 'Function', 'Membership', 'Union', 'Inter', 'SDiff', 'HasSubset', 'Insert',
        'EmptyCollection', 'HAppend', 'id', 'Singleton') or base.startswith('@')


rows_out = []
missing = []
for hol in sorted(consts):
    ty = consts[hol]
    nm = hol.split('$', 1)[1]
    if hol in over:
        lean, perm, st, note = over[hol]
        rows_out.append(('CONST', hol, lean, perm, st, note))
        if not known_core(lean):
            missing.append((hol, lean))
        continue
    if hol in core:
        lean, perm, st, note = core[hol]
        rows_out.append(('CONST', hol, lean, perm, st, note))
        for n in lean.split(','):
            if not known_core(n):
                missing.append((hol, n))
        continue
    if nm.endswith('_CASE'):
        rows_out.append(('CONST', hol, '@match', '', 'convention', 'case construct: Lean matcher (rule CASE)'))
        continue
    if '.seldef.' in nm:
        parts = nm.split('.')
        R, f = parts[1], parts[3]
        if f.endswith('_fupd'):
            rows_out.append(('CONST', hol, '@fupd', '', 'convention', 'record update `s with f := e` (rule REC)'))
        else:
            ln = NS + R + '.' + f
            rows_out.append(('CONST', hol, ln, '', 'convention', 'record field accessor env.v, st.clock (CONVENTIONS)'))
            if ln not in defs:
                missing.append((hol, ln))
        continue
    lean = None
    for c in ctor_candidates(hol, ty):
        if c in defs and defs[c]['kind'] == 'ctor':
            lean = c
    if lean:
        rows_out.append(('CONST', hol, lean, '', 'convention', 'constructor in the namespace of its type (CONVENTIONS)'))
        continue
    lean = NS + nm
    rows_out.append(('CONST', hol, lean, '', 'convention', 'same name (CONVENTIONS: a name not in the rename table is identical)'))
    if lean not in defs:
        missing.append((hol, lean))

extra = []
if LESS:
    extra.append(('CONST', 'list$isPREFIX', 'CmlTS.IS_PREFIX', '1,0', 'convention', 'section 2: IS_PREFIX a b is isPREFIX b a'))
if SON:
    extra.append(('CONST', 'list$isPREFIX', 'IS_PREFIX', '1,0', 'convention', 'section 3: IS_PREFIX l1 l2 is isPREFIX l2 l1'))
    extra.append(('CONST', '@lmem', 'MEM', '', 'convention', 'rule LMEM: MEM x l'))
extra.append(('CONST', '@singleton', 'Singleton.singleton', '', 'convention', 'rule SING: {x} is x INSERT {}'))

unf = [('UNFOLD', '', NS + 'Set', '', 'convention', 'Set alpha := alpha -> Prop (CONVENTIONS: a def for alpha -> Prop)')]
allow = [('ALLOW', '', NS + 'ARB', '', 'convention', 'ARB is Classical.choice (unspecified value)')]
ids = []
if OPUS:
    ids = [('ID', '', 'Decidable.decide', '', 'convention', "proposition used as bool data: Eq_val (decide (b = b')) is HOL4 Eq_val (b = b')")]

if LESS:
    ren = [('typeSysProps$type_subst', 'type_subst_thm'), ('semanticPrimitivesProps$concrete_v_list', 'concrete_v_list_thm'),
           ('typeSysProps$tveLookup_freevars_local', 'tveLookup_freevars_2'), ('typeSound$EVERY_LIST_REL_local', 'EVERY_LIST_REL_2')]
    rnote = 'CONVENTIONS section 7: renamed theorem; the second occurrence (HOL4 export name _local) gets suffix _2'
    rstat = 'convention'
elif NOLESS:
    ren = [('typeSysProps$type_subst', 'type_subst_thm'), ('semanticPrimitivesProps$concrete_v_list', 'concrete_v_list_thm'),
           ('typeSysProps$tveLookup_freevars_local', 'tveLookup_freevars_lem'), ('typeSound$EVERY_LIST_REL_local', 'EVERY_LIST_REL_lem')]
    rnote = 'CONVENTIONS section 4: renamed theorem; the local (second) one gets suffix _lem'
    rstat = 'convention'
else:
    ren = [('typeSysProps$type_subst', 'type_subst_thm'), ('semanticPrimitivesProps$concrete_v_list', 'concrete_v_list_eq'),
           ('typeSysProps$tveLookup_freevars_local', "tveLookup_freevars'"), ('typeSound$EVERY_LIST_REL_local', "EVERY_LIST_REL'")]
    rnote = 'renamed theorem: sonnet CONVENTIONS do not state the four renames; names found in the Lean theorem list'
    rstat = 'lookup'
names = [('NS', '', NS, '', 'convention', 'namespace prefix of theorem and constant names')]
names += [('NAME', h, l, '', rstat, rnote) for h, l in ren]

rules = [
    ('RULE', 'VARS', '', '', 'convention', 'HOL4 free variables are implicitly universal; runs of same-kind binders are order-insensitive'),
    ('RULE', 'IMP', '', '', 'convention', 'A /\\ B ==> C is A ==> B ==> C'),
    ('RULE', 'FLAT', '', '', 'convention', 'and/or chains flattened; Iff is Eq on Prop; Ne is Not Eq'),
    ('RULE', 'NUM', '', '', 'convention', 'numerals are one literal node; SUC n is n + 1; Lean numerals at Int are int_of_num n'),
    ('RULE', 'UNCURRY', '', '', 'convention', 'UNCURRY f p and pair matchers are projections'),
    ('RULE', 'INST', '', '', 'convention', 'instance arguments ignored; extra instance binders compared with the classes of the mapped constants'),
    ('RULE', 'TYVARS', '', '', 'convention', 'type variables renamed by first occurrence; reducible abbreviations unfolded'),
    ('RULE', 'CASE', '', '', 'convention', 'HOL4 X_CASE constants and Lean matchers are one case node, alternatives in constructor order'),
    ('RULE', 'REC', '', '', 'convention', 'record update: HOL4 f_fupd (K e) s and Lean mk with projections of s are one update node; no-op updates dropped'),
    ('RULE', 'BOOL', '', '', 'convention', 'decide p is p; b = true is b (Bool data used as a proposition); Bool.true/false are T/F'),
    ('RULE', 'KRED', '', '', 'convention', 'K x y is x, K x is a constant lambda (definition of K)'),
    ('RULE', 'SING', '', '', 'convention', '{x} is x INSERT {}'),
    ('RULE', 'LMEM', '', '', 'convention', 'MEM x l is x IN LIST_TO_SET l (the HOL4 export has no MEM constant); Lean x in l is the same'),
]
if not SON:
    rules.append(('RULE', 'ZIPPAIR', '', '', 'convention', 'HOL4 ZIP (a,b) is Lean List.zip a b'))

with open(outp, 'w', encoding='utf-8', newline='\n') as f:
    f.write('# S0 map v0 for %s (generated by build_map.py: CONVENTIONS.md + HOL4 constant names + Lean name existence)\n' % run)
    f.write('# lean field: comma list of Lean names; Name#Inst restricts to applications whose instance args include Inst; names starting with @ are rules in scan.py.\n')
    f.write('kind\thol4\tlean\tperm\tstatus\tnote\n')
    for r in names + type_rows + rows_out + extra + unf + allow + ids + rules:
        f.write('\t'.join(r) + '\n')
print(run, 'const rows', len(rows_out), 'type rows', len(type_rows), 'missing names:', len(missing))
for m in missing:
    print('  MISSING', m)
