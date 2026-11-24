"""Apply the 12 self-test mutations to a SCRATCH COPY of the Lean base (never to the base).
usage: python mutate.py SCRATCH_PROJECT_DIR   (then `lake build` there and run ../run.sh on it)
Each mutation edits exactly one theorem statement of one file; writes ../mutations.tsv next to the project."""
import io, sys

root = sys.argv[1]
M = [
    ('M01-dropped-hypothesis', 'Mlstring.lean', 'explode_aux_thm',
     "      n + max = ls.length →\n      explode_aux (implode ls) n max = List.drop n ls",
     "      explode_aux (implode ls) n max = List.drop n ls"),
    ('M03-changed-constant', 'Mllist.lean', 'mergesortN_tail_MEM',
     "x ∈ List.take length lst) := by", "x ∈ List.drop length lst) := by"),
    ('M04-off-by-one', 'Misc.lean', 'LENGTH_FIELDS',
     "(FILTER P ls).length + 1 := by", "(FILTER P ls).length + 2 := by"),
    ('M05-strengthened-conclusion', 'HolSyntaxExtra2.lean', 'type_ok_TYPE_SUBST',
     "      → type_ok s (TYPE_SUBST tyin ty) := by", "      → type_ok s (TYPE_SUBST tyin ty) ∧ type_ok s ty := by"),
    ('M06-changed-type', 'Misc.lean', 'is_subseq_refl',
     "theorem is_subseq_refl {α : Type u} : ∀ (ls : List α), is_subseq ls ls := by",
     "theorem is_subseq_refl : ∀ (ls : List Nat), is_subseq ls ls := by"),
    ('M07-weaker-conclusion', 'Mlstring.lean', 'strcat_nil',
     "theorem strcat_nil (s : mlstring) : strcat (mls \"\") s = s ∧ strcat s (mls \"\") = s := by",
     "theorem strcat_nil (s : mlstring) : strcat (mls \"\") s = s := by"),
    ('M08-swapped-arguments', 'Mlstring.lean', 'mlstring_common_suffix',
     "strcat t1 s = strcat t2 s ↔ t1 = t2 := by", "strcat s t1 = strcat t2 s ↔ t1 = t2 := by"),
    ('M09-lt-to-le', 'Misc.lean', 'w2n_lt_256',
     "∀ (w : word8), w2n w < 256 := by", "∀ (w : word8), w2n w ≤ 256 := by"),
    ('M10-and-to-or-in-hypothesis', 'HolSyntaxExtra.lean', 'VSUBST_WELLTYPED',
     "      welltyped tm ∧\n      (∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →\n      welltyped (VSUBST ilist tm) := by",
     "      welltyped tm ∨\n      (∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →\n      welltyped (VSUBST ilist tm) := by"),
    ('M11-extra-instance-hypothesis', 'Mllist.lean', 'sort_PERM',
     "theorem sort_PERM {α : Type u} :", "theorem sort_PERM {α : Type u} [DecidableEq α] :"),
    ('M12-trivialised-conclusion', 'Misc.lean', 'CHR_w2n_n2w_ORD_simp',
     "CHR (w2n ((n2w : Nat → word8) (ORD c))) = c := by", "c = c := by"),
]
log = []
for tag, f, thm, old, new in M:
    p = root + '/CandleLean/' + f
    s = io.open(p, encoding='utf-8', newline='').read()
    if s.count(old) != 1:
        print('FAIL', tag, s.count(old))
        continue
    io.open(p, 'w', encoding='utf-8', newline='').write(s.replace(old, new))
    log.append((tag, thm, f))
    print('ok', tag, thm)

# M02 (swapped quantifier): the theorem parameters x ty t and the existential n swap places: exists n, forall x ty t, ...
p = root + '/CandleLean/HolSyntax.lean'
t = io.open(p, encoding='utf-8', newline='').read()
a = t.index('theorem PRIMED_NAME_EXISTS (x : string)')
b = t.index(':= by sorry', a)
body = t[a:b].split('\n')[1].strip()
ex, fa = '∃ n, ', '∀ '
assert body.startswith(ex)
new = 'theorem PRIMED_NAME_EXISTS :\n    ' + ex + fa + '(x : string) (ty : type) (t : term), ' + body[len(ex):]
io.open(p, 'w', encoding='utf-8', newline='').write(t[:a] + new + t[b:])
log.append(('M02-swapped-quantifier', 'PRIMED_NAME_EXISTS', 'HolSyntax.lean'))
print('ok M02-swapped-quantifier')
io.open(root + '/../mutations.tsv', 'w', encoding='utf-8').write('\n'.join('\t'.join(x) for x in log) + '\n')
