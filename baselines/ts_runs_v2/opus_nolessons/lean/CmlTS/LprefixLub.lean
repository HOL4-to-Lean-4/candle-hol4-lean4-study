import CmlTS.Prelude.Llist
/-
  Translation of HOL4 theory `lprefix_lub` (lprefix_lubScript.sml).
-/
set_option autoImplicit false

namespace CmlTS

/- HOL4:
Definition lprefix_lub_def:
  lprefix_lub ls lub ⇔
    (!ll. ll ∈ ls ⇒ LPREFIX ll lub) ∧
    (∀ub. (!ll. ll ∈ ls ⇒ LPREFIX ll ub) ⇒ LPREFIX lub ub)
End -/
def lprefix_lub {α : Type} (ls : Set (llist α)) (lub : llist α) : Prop :=
  (∀ ll, ll ∈ ls → LPREFIX ll lub) ∧
  (∀ ub, (∀ ll, ll ∈ ls → LPREFIX ll ub) → LPREFIX lub ub)

end CmlTS
