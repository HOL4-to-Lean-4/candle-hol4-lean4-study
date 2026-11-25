# fitted edits made after looking at the v0 disagreements (exec'd by fit_maps.py; `edits` and `RUNS` are in scope)
RULES_FITTED = [
    ('PAIRN', 'rule PAIRN (fitted): a tuple pattern with n > 2 components is one matcher alternative; parameters are right-nested FST/SND projections (needed for fun (x, _, _) => x, HOL4 shows FST)'),
    ('ETAQ', 'rule ETAQ (fitted): the kernel stores !x. P x eta-contracted as $! P (also ?); expanded to a binder on the HOL4 side'),
    ('RECMK', 'rule RECMK (fitted): a HOL4 record literal is an update of ARB that sets every field; Lean Struct.mk with no common root is the same record literal; a literal made of projections of one record is that record'),
    ('TDEF', 'rule TDEF (fitted): Texn = Tapp [] Texn_num, Tref t = Tapp [t] Tref_num, Tfn a b = Tapp [a; b] Tfn_num, ... (definitions of typeSystem), applied on both sides'),
]
for r in RUNS:
    for nm, note in RULES_FITTED:
        edits[r].append(('add', 'RULE', nm, '', '', note))

nm_note = 'fitted: the export names the [local] copy EVERY_LIST_REL_local; the Lean theorem that quotes `EVERY_LIST_REL[local]` (the generic one, line 50) is the match, not the second-by-line one assumed in v0'
edits['opus_lessons'] += [
    ('add', 'NAME', 'typeSound$EVERY_LIST_REL', 'EVERY_LIST_REL_2', '', nm_note),
    ('set', 'NAME', 'typeSound$EVERY_LIST_REL_local', 'EVERY_LIST_REL', '', nm_note),
]
edits['sonnet_lessons'] += [
    ('add', 'NAME', 'typeSound$EVERY_LIST_REL', "EVERY_LIST_REL'", '', nm_note),
    ('set', 'NAME', 'typeSound$EVERY_LIST_REL_local', 'EVERY_LIST_REL', '', nm_note),
]
