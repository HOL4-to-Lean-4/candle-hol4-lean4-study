import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

variable {U : Type u}

def is_interpretation0 (mem : U → U → Prop) (sig : sig) (int : interpretation U) : Prop :=
  is_type_assignment0 mem (tysof sig) (tyaof int) ∨
  is_term_assignment0 mem (tmsof sig) (tyaof int) (tmaof int)

theorem FDOM_FUPDATE_aux {α : Type u} {β : Type v} (f : fmap α β) (p : α × β) :
    p.1 ∈ FDOM (FUPDATE f p) := by
  simp [FDOM, FUPDATE, Aux.mem_def]

theorem witness : ¬ ∀ (mem : Bool → Bool → Prop) (sig : sig) (int : interpretation Bool),
    (Mut.is_interpretation0 mem sig int ↔ Candle.is_interpretation0 mem sig int) := by
  intro h
  let sg : sig := (FUPDATE FEMPTY (mls "c", 0), FEMPTY)
  let it : interpretation Bool := (fun _ _ => true, fun _ _ => true)
  have hB : is_term_assignment0 (fun (_ _ : Bool) => False) (tmsof sg) (tyaof it) (tmaof it) := by
    intro x hx
    exact absurd rfl hx
  have hm : Mut.is_interpretation0 (fun (_ _ : Bool) => False) sg it := Or.inr hB
  have hb := (h (fun _ _ => False) sg it).1 hm
  have hA := hb.1 (mls "c") (FDOM_FUPDATE_aux FEMPTY (mls "c", 0))
  have hA2 := hA []
  simp [FAPPLY, FUPDATE, EVERY, inhabited, sg, it, tysof, tyaof] at hA2

end Mut

#print axioms Mut.witness
