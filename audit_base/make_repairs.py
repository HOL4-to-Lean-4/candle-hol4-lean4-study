"""Repair conservativity violations (tiers 1 and 2) in a copy of the Opus with-lessons baseline.

Run from audit_base/ after copying ../baselines/opus55_direct_translation/lean here.
"""
import io
import re

R = "lean/CandleLean/"


def load(f):
    return io.open(R + f, encoding="utf-8").read()


def save(f, t):
    io.open(R + f, "w", encoding="utf-8", newline="\n").write(t)


def rep1(t, a, b, f=""):
    assert t.count(a) == 1, (f, t.count(a), a[:80])
    return t.replace(a, b)


def edit(f, pairs):
    t = load(f)
    for a, b in pairs:
        t = rep1(t, a, b, f)
    save(f, t)


# ---- Prelude/Basic: ARB is an undefined constant in HOL4 (new_constant, no axiom)
edit("Prelude/Basic.lean", [(
    """/- HOL4: bool$ARB
     ARB = @x. F
   (HOL4 pattern completion fills missing cases of a `Definition` with `ARB`). -/
def ARB {α : Sort u} [Nonempty α] : α := Classical.epsilon (fun _ : α => False)""",
    """/- HOL4: bool$ARB    new_constant("ARB", alpha): no defining theorem. -/
opaque ARB {α : Sort u} [Nonempty α] : α""")])

# ---- Prelude/List: HD, LAST, SEG
edit("Prelude/List.lean", [
    ("""/- HOL4: list$HD    Definition HD: HD (h::t) = h  (pattern completion: HD [] = ARB) -/
def HD {α : Type u} [Nonempty α] : List α → α
  | h :: _ => h
  | [] => ARB
""",
     """/- HOL4: list$HD    Definition HD: HD (h::t) = h   (HD [] is unspecified) -/
private opaque HD_pkg {α : Type u} [Nonempty α] : {f : List α → α // ∀ h t, f (h :: t) = h} :=
  ⟨fun l => match l with | h :: _ => h | [] => Classical.choice inferInstance, fun _ _ => rfl⟩

def HD {α : Type u} [Nonempty α] : List α → α := HD_pkg.1

/-- The HOL4 defining theorem of `HD`. -/
theorem HD_def {α : Type u} [Nonempty α] (h : α) (t : List α) : HD (h :: t) = h := HD_pkg.2 h t
"""),
    ("""/- HOL4: list$LAST    LAST (h::t) = if t = [] then h else LAST t
   (pattern completion: LAST [] = ARB) -/
def LAST {α : Type u} [Nonempty α] : List α → α
  | [] => ARB
  | h :: t => if t = [] then h else LAST t
""",
     """/- HOL4: list$LAST    LAST (h::t) = if t = [] then h else LAST t   (LAST [] is unspecified) -/
private def LAST_wit {α : Type u} [Nonempty α] : List α → α
  | [] => Classical.choice inferInstance
  | h :: t => if t = [] then h else LAST_wit t

private opaque LAST_pkg {α : Type u} [Nonempty α] :
    {f : List α → α // ∀ h t, f (h :: t) = if t = [] then h else f t} :=
  ⟨LAST_wit, fun _ _ => by simp [LAST_wit]⟩

def LAST {α : Type u} [Nonempty α] : List α → α := LAST_pkg.1

/-- The HOL4 defining theorem of `LAST`. -/
theorem LAST_DEF {α : Type u} [Nonempty α] (h : α) (t : List α) :
    LAST (h :: t) = if t = [] then h else LAST t := LAST_pkg.2 h t
"""),
    ("""   Encoded as Hilbert choice of a function satisfying the specification
   (`SEG (SUC m) k []` is unspecified, as in HOL4). -/""",
     """   (`SEG (SUC m) k []` is unspecified, as in HOL4). -/"""),
    ("""def SEG {α : Type u} : Nat → Nat → List α → List α :=
  Classical.epsilon (SEG_spec (α := α))

/-- The HOL4 defining theorem of `SEG` (HOL4 `SEG`, from `new_specification`). -/
theorem SEG_def {α : Type u} : SEG_spec (SEG (α := α)) := by
  apply Classical.epsilon_spec (p := SEG_spec (α := α))
""",
     """private theorem SEG_exists {α : Type u} : ∃ f, SEG_spec (α := α) f := by
"""),
    ("""  · intro m x l; simp
  · intro m k x l; simp
""",
     """  · intro m x l; simp
  · intro m k x l; simp

private opaque SEG_pkg {α : Type u} : {f : Nat → Nat → List α → List α // SEG_spec f} :=
  ⟨Classical.choose SEG_exists, Classical.choose_spec SEG_exists⟩

def SEG {α : Type u} : Nat → Nat → List α → List α := SEG_pkg.1

/-- The HOL4 defining theorem of `SEG` (HOL4 `SEG`, from `new_specification`). -/
theorem SEG_def {α : Type u} : SEG_spec (SEG (α := α)) := SEG_pkg.2
"""),
])

# ---- Prelude/String: CHR
edit("Prelude/String.lean", [(
    """   `CHR n` for `n >= 256` is unspecified in HOL4; here it is `(ARB : Nat → char) n`. -/
def CHR (n : Nat) : char :=
  if h : n < 256 then ⟨n, h⟩ else (ARB : Nat → char) n
""",
    """   (`CHR n` for `n >= 256` is unspecified) -/
private opaque CHR_pkg : {f : Nat → char // ∀ n (h : n < 256), f n = ⟨n, h⟩} :=
  ⟨fun n => if h : n < 256 then ⟨n, h⟩ else ⟨0, by decide⟩, fun n h => by simp [h]⟩

def CHR : Nat → char := CHR_pkg.1

/-- `CHR` on its domain. -/
theorem CHR_of_lt {n : Nat} (h : n < 256) : CHR n = ⟨n, h⟩ := CHR_pkg.2 n h
""")])

# ---- Prelude/FiniteMap: FAPPLY outside the domain, FUN_FMAP
edit("Prelude/FiniteMap.lean", [
    ("""/- HOL4: finite_map$FAPPLY (overloaded as ')    FAPPLY (f:'a |-> 'b) x = OUTL (fmap_REP f x)
   (`OUTL (INR _)` is unspecified in HOL4: here `ARB`, the same value for every map and key,
   as in HOL4 where it is the fixed value `OUTL (INR one)`) -/
""",
     """/-- HOL4's `OUTL (INR one)`: a fixed but unspecified value. -/
private opaque FAPPLY_outside {β : Type v} [Nonempty β] : β

/- HOL4: finite_map$FAPPLY (overloaded as ')    FAPPLY (f:'a |-> 'b) x = OUTL (fmap_REP f x)
   (`OUTL (INR one)` is the same unspecified value for every map and key) -/
"""),
    ("  | none => ARB\n", "  | none => FAPPLY_outside\n"),
    ("""def FUN_FMAP {α : Type u} {β : Type v} [Nonempty β] : (α → β) → Set α → fmap α β :=
  Classical.epsilon (FUN_FMAP_spec (α := α) (β := β))

/-- The HOL4 defining theorem `FUN_FMAP_DEF`. -/
theorem FUN_FMAP_DEF {α : Type u} {β : Type v} [Nonempty β] :
    FUN_FMAP_spec (FUN_FMAP (α := α) (β := β)) := by
  apply Classical.epsilon_spec (p := FUN_FMAP_spec (α := α) (β := β))
""",
     """private theorem FUN_FMAP_exists {α : Type u} {β : Type v} [Nonempty β] :
    ∃ F, FUN_FMAP_spec (α := α) (β := β) F := by
"""),
    ("""    have hx' : P x := hx
    simp [FAPPLY, hx']
""",
     """    have hx' : P x := hx
    simp [FAPPLY, hx']

private opaque FUN_FMAP_pkg {α : Type u} {β : Type v} [Nonempty β] :
    {F : (α → β) → Set α → fmap α β // FUN_FMAP_spec F} :=
  ⟨Classical.choose FUN_FMAP_exists, Classical.choose_spec FUN_FMAP_exists⟩

def FUN_FMAP {α : Type u} {β : Type v} [Nonempty β] : (α → β) → Set α → fmap α β :=
  FUN_FMAP_pkg.1

/-- The HOL4 defining theorem `FUN_FMAP_DEF`. -/
theorem FUN_FMAP_DEF {α : Type u} {β : Type v} [Nonempty β] :
    FUN_FMAP_spec (FUN_FMAP (α := α) (β := β)) := FUN_FMAP_pkg.2
"""),
])
t = load("Prelude/FiniteMap.lean")
t = t.replace("""   Encoded as Hilbert choice of a function satisfying the specification. -/
def FUN_FMAP_spec""", """-/
def FUN_FMAP_spec""")
save("Prelude/FiniteMap.lean", t)

# ---- HolSyntaxLib: RESULT, CLASH
edit("HolSyntaxLib.lean", [
    ("""   (pattern completion: RESULT (Clash t) = ARB) -/
def RESULT {α : Type u} : result α → α
  | Result t => t
  | Clash t => @ARB α ⟨t⟩
""",
     """   (`RESULT (Clash t)` is unspecified) -/
private opaque RESULT_pkg {α : Type u} : {f : result α → α // ∀ t, f (Result t) = t} :=
  ⟨fun r => match r with | Result t => t | Clash t => t, fun _ => rfl⟩

def RESULT {α : Type u} : result α → α := RESULT_pkg.1

theorem RESULT_def {α : Type u} (t : α) : RESULT (Result t) = t := RESULT_pkg.2 t
"""),
    ("""   (pattern completion: CLASH (Result t) = ARB) -/
def CLASH {α : Type u} : result α → α
  | Clash t => t
  | Result t => @ARB α ⟨t⟩
""",
     """   (`CLASH (Result t)` is unspecified) -/
private opaque CLASH_pkg {α : Type u} : {f : result α → α // ∀ t, f (Clash t) = t} :=
  ⟨fun r => match r with | Clash t => t | Result t => t, fun _ => rfl⟩

def CLASH {α : Type u} : result α → α := CLASH_pkg.1

theorem CLASH_def {α : Type u} (t : α) : CLASH (Clash t) = t := CLASH_pkg.2 t
"""),
])

# ---- HolSyntax: dest_var, VARIANT_PRIMES
t = load("HolSyntax.lean")
i = t.index("   (pattern completion: dest_var of a non-variable is ARB) -/")
end = "  | Abs _ _ => ARB\n"
j = t.index(end, i) + len(end)
t = t[:i] + """   (`dest_var` of a non-variable is unspecified) -/
private opaque dest_var_pkg : {f : term → mlstring × type // ∀ x ty, f (Var x ty) = (x, ty)} :=
  ⟨fun t => match t with | Var x ty => (x, ty) | _ => default, fun _ _ => rfl⟩

def dest_var : term → mlstring × type := dest_var_pkg.1

theorem dest_var_def (x : mlstring) (ty : type) : dest_var (Var x ty) = (x, ty) :=
  dest_var_pkg.2 x ty
""" + t[j:]
t = rep1(t, """def VARIANT_PRIMES : term → string → type → Nat :=
  Classical.epsilon VARIANT_PRIMES_spec
""", "")
t = rep1(t, """/-- The HOL4 defining theorem `VARIANT_PRIMES_def` (from `new_specification`). -/
theorem VARIANT_PRIMES_def : VARIANT_PRIMES_spec VARIANT_PRIMES := by
  apply Classical.epsilon_spec (p := VARIANT_PRIMES_spec)
""", "private theorem VARIANT_PRIMES_exists : ∃ f, VARIANT_PRIMES_spec f := by\n")
t = rep1(t, """    fun t x ty => Classical.choose_spec (this t x ty)⟩
""", """    fun t x ty => Classical.choose_spec (this t x ty)⟩

private opaque VARIANT_PRIMES_pkg : {f : term → string → type → Nat // VARIANT_PRIMES_spec f} :=
  ⟨Classical.choose VARIANT_PRIMES_exists, Classical.choose_spec VARIANT_PRIMES_exists⟩

def VARIANT_PRIMES : term → string → type → Nat := VARIANT_PRIMES_pkg.1

/-- The HOL4 defining theorem `VARIANT_PRIMES_def` (from `new_specification`). -/
theorem VARIANT_PRIMES_def : VARIANT_PRIMES_spec VARIANT_PRIMES := VARIANT_PRIMES_pkg.2
""")
save("HolSyntax.lean", t)

# ---- HolSyntaxExtra: fresh
edit("HolSyntaxExtra.lean", [
    ("""def fresh : Set string → string := Classical.epsilon fresh_spec

/-- The HOL4 defining theorem `fresh_def` (from `new_specification`). -/
theorem fresh_def : fresh_spec fresh := by
  apply Classical.epsilon_spec (p := fresh_spec)
""", """private theorem fresh_exists : ∃ f, fresh_spec f := by
"""),
    ("""  exact ⟨fun s => Classical.choose (this s), fun s => Classical.choose_spec (this s)⟩
""", """  exact ⟨fun s => Classical.choose (this s), fun s => Classical.choose_spec (this s)⟩

private opaque fresh_pkg : {f : Set string → string // fresh_spec f} :=
  ⟨Classical.choose fresh_exists, Classical.choose_spec fresh_exists⟩

def fresh : Set string → string := fresh_pkg.1

/-- The HOL4 defining theorem `fresh_def` (from `new_specification`). -/
theorem fresh_def : fresh_spec fresh := fresh_pkg.2
"""),
])

# ---- HolSemantics: instance_
t = load("HolSemantics.lean")
t = rep1(t, """def instance_ : tmsig → interpretation U → mlstring → type → tyval U → U :=
  @Classical.epsilon _ ⟨fun _ i name _ _ => tmaof i name []⟩ instance_spec

/-- The HOL4 defining theorem `instance_def` (from `new_specification`). -/
theorem instance_def : instance_spec (U := U) instance_ := by
  apply Classical.epsilon_spec (p := instance_spec)
""", "private theorem instance_exists : ∃ f, instance_spec (U := U) f := by\n")
m = re.search(r"private theorem instance_exists.*?\n\n", t, flags=re.S)
t = t[:m.end()] + """private opaque instance_pkg {U : Type u} :
    {f : tmsig → interpretation U → mlstring → type → tyval U → U // instance_spec f} :=
  ⟨Classical.choose instance_exists, Classical.choose_spec instance_exists⟩

def instance_ : tmsig → interpretation U → mlstring → type → tyval U → U := instance_pkg.1

/-- The HOL4 defining theorem `instance_def` (from `new_specification`). -/
theorem instance_def : instance_spec (U := U) instance_ := instance_pkg.2

""" + t[m.end():]
save("HolSemantics.lean", t)

# ---- fallout in auxiliary proofs (no statement or definition changes)
edit("Mlstring.lean", [("  | 0, a :: t, _ => by simp [EL, HD]\n", "  | 0, a :: t, _ => by simp [EL, HD_def]\n")])

# ---- HolSemantics: termsem0. HOL4 saves only termsem_def (4 clauses); no ARB clause is available.
t = load("HolSemantics.lean")
i = t.index("   (pattern completion: termsem0 of `Abs v b`")
j = t.index("def termsem0", i)
k = t.index("  | v, Abs (Abs _ _) _ => @ARB U ⟨tmvof v default⟩\n", j) + len("  | v, Abs (Abs _ _) _ => @ARB U ⟨tmvof v default⟩\n")
old = t[j:k]
wit = old.replace("def termsem0", "private def termsem0_wit").replace("termsem0 mem tmsig i", "termsem0_wit mem tmsig i")
new_pkg = wit + """
private theorem termsem0_exists (mem : U → U → Prop) (tmsig : tmsig) (i : interpretation U) :
    ∃ f : valuation U → term → U,
      (∀ v x ty, f v (Var x ty) = tmvof v (x, ty)) ∧
      (∀ v name ty, f v (Const name ty) = instance_ tmsig i name ty (tyvof v)) ∧
      (∀ v t1 t2, f v (Comb t1 t2) = apply mem (f v t1) (f v t2)) ∧
      (∀ v x ty b, f v (Abs (Var x ty) b) =
        abstract mem (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
          (fun m => f (tyvof v, UPDATE (x, ty) m (tmvof v)) b)) :=
  ⟨termsem0_wit mem tmsig i, fun _ _ _ => by simp [termsem0_wit], fun _ _ _ => by simp [termsem0_wit],
    fun _ _ _ => by simp [termsem0_wit], fun _ _ _ _ => by simp [termsem0_wit]⟩

private opaque termsem0_pkg (mem : U → U → Prop) (tmsig : tmsig) (i : interpretation U) :
    {f : valuation U → term → U //
      (∀ v x ty, f v (Var x ty) = tmvof v (x, ty)) ∧
      (∀ v name ty, f v (Const name ty) = instance_ tmsig i name ty (tyvof v)) ∧
      (∀ v t1 t2, f v (Comb t1 t2) = apply mem (f v t1) (f v t2)) ∧
      (∀ v x ty b, f v (Abs (Var x ty) b) =
        abstract mem (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
          (fun m => f (tyvof v, UPDATE (x, ty) m (tmvof v)) b))} :=
  ⟨Classical.choose (termsem0_exists mem tmsig i), Classical.choose_spec (termsem0_exists mem tmsig i)⟩

def termsem0 (mem : U → U → Prop) (tmsig : tmsig) (i : interpretation U) :
    valuation U → term → U := (termsem0_pkg mem tmsig i).1

/-- The HOL4 theorem `termsem_def`. -/
theorem termsem0_def (mem : U → U → Prop) (tmsig : tmsig) (i : interpretation U) :
      (∀ v x ty, termsem0 mem tmsig i v (Var x ty) = tmvof v (x, ty)) ∧
      (∀ v name ty, termsem0 mem tmsig i v (Const name ty) = instance_ tmsig i name ty (tyvof v)) ∧
      (∀ v t1 t2, termsem0 mem tmsig i v (Comb t1 t2) =
        apply mem (termsem0 mem tmsig i v t1) (termsem0 mem tmsig i v t2)) ∧
      (∀ v x ty b, termsem0 mem tmsig i v (Abs (Var x ty) b) =
        abstract mem (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
          (fun m => termsem0 mem tmsig i (tyvof v, UPDATE (x, ty) m (tmvof v)) b)) :=
  (termsem0_pkg mem tmsig i).2
"""
t = t[:i] + "   (`termsem0` of `Abs v b` with `v` not a variable is not given by HOL4;\n   `((x,ty) =+ m) f` is `UPDATE (x,ty) m f`) -/\n" + new_pkg + t[k:]
save("HolSemantics.lean", t)
print("repaired")
