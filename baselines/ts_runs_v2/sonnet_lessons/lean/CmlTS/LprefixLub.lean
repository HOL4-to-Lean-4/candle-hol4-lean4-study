import CmlTS.Prelude.Basic
import CmlTS.Prelude.List
import CmlTS.Prelude.Coalg

/-!
# lprefix_lub (HOL4 theory `lprefix_lub`)
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   Definition lprefix_lub_def:
     lprefix_lub ls lub ⇔
       (!ll. ll ∈ ls ⇒ LPREFIX ll lub) ∧
       (∀ub. (!ll. ll ∈ ls ⇒ LPREFIX ll ub) ⇒ LPREFIX lub ub)
   End -/
def lprefix_lub {α : Type u} (ls : Set (llist α)) (lub : llist α) : Prop :=
  (∀ ll, ll ∈ ls → LPREFIX ll lub) ∧
  (∀ ub, (∀ ll, ll ∈ ls → LPREFIX ll ub) → LPREFIX lub ub)

end
