import CmlTS.Ast
import CmlTS.Evaluate
import CmlTS.Namespace
import CmlTS.NamespaceProps
import CmlTS.SemanticPrimitives
import CmlTS.SemanticPrimitivesProps

/-
HOL4 theory `evaluateProps` (evaluatePropsScript.sml).
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {ffi : Type}

/- HOL4:
Definition call_FFI_rel_def:
  call_FFI_rel s1 s2 <=> ?n conf bytes t. call_FFI s1 n conf bytes = FFI_return s2 t
End -/
def call_FFI_rel (s1 s2 : ffi_state ffi) : Prop :=
  ∃ n conf bytes t, call_FFI s1 n conf bytes = FFI_return s2 t

/- HOL4:
Definition dest_IO_event_def[simp]:
  dest_IO_event (IO_event s c b) = (s,c,b)
End -/
def dest_IO_event : io_event → ffiname × List word8 × List (word8 × word8)
  | IO_event s c b => (s, c, b)

/- HOL4:
Definition io_events_mono_def:
  io_events_mono s1 s2 ⇔
    s1.io_events ≼ s2.io_events ∧
    (s2.io_events = s1.io_events ⇒ s2 = s1)
End -/
def io_events_mono (s1 s2 : ffi_state ffi) : Prop :=
  isPREFIX s1.io_events s2.io_events ∧ (s2.io_events = s1.io_events → s2 = s1)

/- HOL4:
Definition is_clock_io_mono_def:
  is_clock_io_mono f s = (case f s of (s', r) =>
        io_events_mono s.ffi s'.ffi
        /\ s'.clock <= s.clock
        /\ s.next_type_stamp <= s'.next_type_stamp
        /\ s.next_exn_stamp <= s'.next_exn_stamp
        /\ LENGTH s.refs <= LENGTH s'.refs
        /\ (!clk. case f (s with clock := clk) of (s'', r') =>
            (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> ~ (r = Rerr (Rabort Rtimeout_error))
                ==> r' = r
                    /\ s'' = (s' with clock := clk - (s.clock - s'.clock)))
            /\ (~ (r = Rerr (Rabort Rtimeout_error))
                ==> (clk >= s.clock - s'.clock
                    <=> ~ (r' = Rerr (Rabort Rtimeout_error))))
            /\ (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> clk <= s.clock
                ==> ~ (r = Rerr (Rabort Rtimeout_error)))
            /\ (clk <= s.clock ==> io_events_mono s''.ffi s'.ffi)
        ))
End -/
def is_clock_io_mono {α β : Type} (f : state ffi → state ffi × result α β) (s : state ffi) :
    Prop :=
  match f s with
  | (s', r) =>
    io_events_mono s.ffi s'.ffi ∧
    s'.clock ≤ s.clock ∧
    s.next_type_stamp ≤ s'.next_type_stamp ∧
    s.next_exn_stamp ≤ s'.next_exn_stamp ∧
    s.refs.length ≤ s'.refs.length ∧
    (∀ clk : Nat,
      match f { s with clock := clk } with
      | (s'', r') =>
        (¬ (r' = Rerr (Rabort Rtimeout_error)) →
          ¬ (r = Rerr (Rabort Rtimeout_error)) →
          r' = r ∧ s'' = { s' with clock := clk - (s.clock - s'.clock) }) ∧
        (¬ (r = Rerr (Rabort Rtimeout_error)) →
          (clk ≥ s.clock - s'.clock ↔ ¬ (r' = Rerr (Rabort Rtimeout_error)))) ∧
        (¬ (r' = Rerr (Rabort Rtimeout_error)) →
          clk ≤ s.clock →
          ¬ (r = Rerr (Rabort Rtimeout_error))) ∧
        (clk ≤ s.clock → io_events_mono s''.ffi s'.ffi))

/- HOL4:
Definition adj_clock_def:
  adj_clock inc dec s = (s with clock := ((s.clock + inc) - dec))
End -/
def adj_clock (inc dec : Nat) (s : state ffi) : state ffi :=
  { s with clock := s.clock + inc - dec }

/-! ## Theorems -/

/- HOL4:
Theorem io_events_mono_trans:
   io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 ⇒
   io_events_mono ffi1 ffi3 -/
theorem io_events_mono_trans (ffi1 ffi2 ffi3 : ffi_state ffi) :
    io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 → io_events_mono ffi1 ffi3 := by
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rw [Aux.isPREFIX_iff] at h1 h3
  obtain ⟨l1, h1⟩ := h1
  obtain ⟨l2, h3⟩ := h3
  refine ⟨Aux.isPREFIX_iff.mpr ⟨l1 ++ l2, by rw [h3, h1, List.append_assoc]⟩, fun h => ?_⟩
  rw [h3, h1, List.append_assoc] at h
  have hl := congrArg List.length h
  simp only [List.length_append] at hl
  have e1 : l1 = [] := List.eq_nil_of_length_eq_zero (by omega)
  have e2 : l2 = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst e1; subst e2
  rw [h4 (by simpa using h3), h2 (by simpa using h1)]

/- HOL4:
Theorem call_FFI_rel_io_events_mono:
   ∀s1 s2.
   RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2 -/
theorem call_FFI_rel_io_events_mono :
    ∀ s1 s2 : ffi_state ffi, RTC call_FFI_rel s1 s2 → io_events_mono s1 s2 := by
  intro s1 s2 h
  induction h with
  | refl x => exact ⟨Aux.isPREFIX_iff.mpr ⟨[], by simp⟩, fun _ => rfl⟩
  | step x y z hxy _ ih =>
    refine io_events_mono_trans x y z ⟨?_, ih⟩
    obtain ⟨n, conf, bytes, t, h⟩ := hxy
    unfold call_FFI at h
    split at h
    · split at h
      · split at h
        · cases h
          refine ⟨Aux.isPREFIX_iff.mpr ⟨_, rfl⟩, fun he => ?_⟩
          simp at he
        · cases h
      · cases h
    · cases h
      exact ⟨Aux.isPREFIX_iff.mpr ⟨[], by simp⟩, fun _ => rfl⟩

/- HOL4:
Theorem io_events_mono_refl[simp]:
   io_events_mono ffi ffi -/
theorem io_events_mono_refl {ffi_ty : Type} (ffi : ffi_state ffi_ty) :
    io_events_mono ffi ffi := ⟨Aux.isPREFIX_iff.mpr ⟨[], by simp⟩, fun _ => rfl⟩

theorem Aux.LUPDATE_length {α : Type} (x : α) : ∀ (l : List α) (n : Nat),
    (LUPDATE x n l).length = l.length := by
  intro l
  induction l with
  | nil => intro n; rfl
  | cons a t ih =>
    intro n
    simp only [LUPDATE]
    split <;> simp [ih]

theorem Aux.store_assign_length {α : Type} {n : Nat} {v : store_v α} {s s' : List (store_v α)}
    (h : store_assign n v s = some s') : s'.length = s.length := by
  unfold store_assign at h
  split at h
  · cases h; exact Aux.LUPDATE_length _ _ _
  · cases h

theorem Aux.store_alloc_length {α : Type} {n : Nat} {v : store_v α} {s s' : List (store_v α)}
    (h : store_alloc v s = (s', n)) : s'.length = s.length + 1 := by
  unfold store_alloc at h
  cases h
  simp

theorem Aux.thunk_op_cases {ffi : Type} {s : List (store_v value)} {t : ffi_state ffi}
    {th : thunk_op_t} {vs : List value} {st' : List (store_v value) × ffi_state ffi}
    {v : result value value} (h : thunk_op (s, t) th vs = some (st', v)) :
    st'.2 = t ∧ s.length ≤ st'.1.length ∧ ∃ r, v = Rval r := by
  unfold thunk_op at h
  dsimp only at h
  split at h
  · cases h
    refine ⟨rfl, ?_, _, rfl⟩
    simp [store_alloc]
  · split at h
    · rename_i hs
      cases h
      exact ⟨rfl, by simp [Aux.store_assign_length hs], _, rfl⟩
    · cases h
  · cases h

theorem Aux.do_app_facts {ffi : Type} {s : List (store_v value)} {t : ffi_state ffi}
    {op : CmlTS.op} {vs : List value} {st' : List (store_v value) × ffi_state ffi}
    {v : result value value} (h : do_app (s, t) op vs = some (st', v)) :
    s.length ≤ st'.1.length ∧
    (st'.2 = t ∨ ∃ n conf bytes ws, call_FFI t n conf bytes = FFI_return st'.2 ws) := by
  rw [do_app_cases] at h
  repeat' (apply Or.elim h <;> clear h <;> intro h)
  all_goals (repeat' (obtain ⟨_, h⟩ := h))
  all_goals subst_vars
  all_goals first
    | exact ⟨Nat.le_refl _, Or.inl rfl⟩
    | (rename_i ha
       exact ⟨Nat.le_of_eq (Aux.store_assign_length ha).symm, Or.inl rfl⟩)
    | (rename_i ha
       have := Aux.store_alloc_length ha
       exact ⟨by dsimp only; omega, Or.inl rfl⟩)
    | (rename_i hc ha
       exact ⟨Nat.le_of_eq (Aux.store_assign_length ha).symm, Or.inr ⟨_, _, _, _, hc⟩⟩)
    | exact ⟨(Aux.thunk_op_cases h).2.1, Or.inl (Aux.thunk_op_cases h).1⟩

/- HOL4:
Theorem do_app_call_FFI_rel:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi' -/
theorem do_app_call_FFI_rel {ffi_ty : Type} (r r' : List (store_v value))
    (ffi ffi' : ffi_state ffi_ty) (op : CmlTS.op) (vs : List value) (res : result value value) :
    do_app (r, ffi) op vs = some ((r', ffi'), res) → RTC call_FFI_rel ffi ffi' := by
  intro h
  rcases (Aux.do_app_facts h).2 with h | h
  · have h : ffi' = ffi := h
    subst h
    exact RTC.refl _
  · exact RTC.step _ _ _ h (RTC.refl _)

/- HOL4:
Theorem do_app_io_events_mono:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi' -/
theorem do_app_io_events_mono {ffi_ty : Type} (r r' : List (store_v value))
    (ffi ffi' : ffi_state ffi_ty) (op : CmlTS.op) (vs : List value) (res : result value value) :
    do_app (r, ffi) op vs = some ((r', ffi'), res) → io_events_mono ffi ffi' :=
  fun h => call_FFI_rel_io_events_mono _ _ (do_app_call_FFI_rel _ _ _ _ _ _ _ h)

theorem Aux.icm_iff {α β : Type} (f : state ffi → state ffi × result α β) (s : state ffi) :
    is_clock_io_mono f s ↔
      (io_events_mono s.ffi (f s).1.ffi ∧
      (f s).1.clock ≤ s.clock ∧
      s.next_type_stamp ≤ (f s).1.next_type_stamp ∧
      s.next_exn_stamp ≤ (f s).1.next_exn_stamp ∧
      s.refs.length ≤ (f s).1.refs.length ∧
      ∀ clk : Nat,
        (¬ ((f { s with clock := clk }).2 = Rerr (Rabort Rtimeout_error)) →
          ¬ ((f s).2 = Rerr (Rabort Rtimeout_error)) →
          (f { s with clock := clk }).2 = (f s).2 ∧ (f { s with clock := clk }).1 =
            { (f s).1 with clock := clk - (s.clock - (f s).1.clock) }) ∧
        (¬ ((f s).2 = Rerr (Rabort Rtimeout_error)) →
          (clk ≥ s.clock - (f s).1.clock ↔
            ¬ ((f { s with clock := clk }).2 = Rerr (Rabort Rtimeout_error)))) ∧
        (¬ ((f { s with clock := clk }).2 = Rerr (Rabort Rtimeout_error)) →
          clk ≤ s.clock →
          ¬ ((f s).2 = Rerr (Rabort Rtimeout_error))) ∧
        (clk ≤ s.clock → io_events_mono (f { s with clock := clk }).1.ffi (f s).1.ffi)) :=
  Iff.rfl

/-- Functions that do not look at the clock. -/
theorem Aux.icm_noclock {α β : Type} {f : state ffi → state ffi × result α β} {s s' : state ffi}
    {r : result α β}
    (h : ∀ clk, f { s with clock := clk } = ({ s' with clock := clk }, r))
    (h1 : io_events_mono s.ffi s'.ffi)
    (h2 : s.next_type_stamp ≤ s'.next_type_stamp)
    (h3 : s.next_exn_stamp ≤ s'.next_exn_stamp)
    (h4 : s.refs.length ≤ s'.refs.length) : is_clock_io_mono f s := by
  rw [Aux.icm_iff]
  have h0 : f s = ({ s' with clock := s.clock }, r) := h s.clock
  rw [h0]
  refine ⟨h1, Nat.le_refl _, h2, h3, h4, fun clk => ?_⟩
  rw [h clk]
  refine ⟨fun _ _ => ⟨rfl, ?_⟩, fun hr => ⟨fun _ => hr, fun _ => ?_⟩, fun hr _ => hr,
    fun _ => io_events_mono_refl _⟩
  · simp
  · simp

theorem Aux.icm_ret {α β : Type} (r : result α β) (s : state ffi) :
    is_clock_io_mono (fun s : state ffi => (s, r)) s :=
  Aux.icm_noclock (s' := s) (fun _ => rfl) (io_events_mono_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _)

/- HOL4:
Theorem is_clock_io_mono_cong:
  s = t ==>
  (!s. s.eval_state = t.eval_state /\ s.refs = t.refs /\ s.ffi = t.ffi ==>
    f s = g s) ==>
  (is_clock_io_mono f s <=> is_clock_io_mono g t) -/
theorem is_clock_io_mono_cong {α β : Type} (s t : state ffi)
    (f g : state ffi → state ffi × result α β) :
    s = t →
    (∀ s : state ffi, s.eval_state = t.eval_state ∧ s.refs = t.refs ∧ s.ffi = t.ffi →
      f s = g s) →
    (is_clock_io_mono f s ↔ is_clock_io_mono g t) := by
  rintro rfl h
  rw [Aux.icm_iff, Aux.icm_iff, h s ⟨rfl, rfl, rfl⟩]
  have h' : ∀ clk, f { s with clock := clk } = g { s with clock := clk } :=
    fun clk => h _ ⟨rfl, rfl, rfl⟩
  simp only [h']

/- HOL4:
Theorem is_clock_io_mono_return:
   is_clock_io_mono (\s. (s,Rval r)) s -/
theorem is_clock_io_mono_return {α β : Type} (r : α) (s : state ffi) :
    is_clock_io_mono (fun s : state ffi => (s, (Rval r : result α β))) s := Aux.icm_ret _ _

/- HOL4:
Theorem is_clock_io_mono_err:
   is_clock_io_mono (\s. (s,Rerr r)) s -/
theorem is_clock_io_mono_err {α β : Type} (r : error_result β) (s : state ffi) :
    is_clock_io_mono (fun s : state ffi => (s, (Rerr r : result α β))) s := Aux.icm_ret _ _

/- HOL4:
Theorem pair_CASE_eq_forall:
   (case x of (a, b) => P a b) = (!a b. x = (a, b) ==> P a b) -/
theorem pair_CASE_eq_forall {α β : Type} (x : α × β) (P : α → β → Prop) :
    (match x with | (a, b) => P a b) ↔ (∀ a b, x = (a, b) → P a b) := by
  obtain ⟨a, b⟩ := x
  constructor
  · intro h a' b' he; cases he; exact h
  · intro h; exact h a b rfl

/- HOL4:
Theorem is_clock_io_mono_bind:
   is_clock_io_mono f s /\ (!s' r. f s = (s', r)
        ==> is_clock_io_mono (g r) s')
    /\ (!s'. g (Rerr (Rabort Rtimeout_error)) s'
        = (s', Rerr (Rabort Rtimeout_error)))
    ==> is_clock_io_mono (\s. case f s of (s', r) => g r s') s -/
theorem is_clock_io_mono_bind {α β γ δ : Type} (f : state ffi → state ffi × result α β)
    (g : result α β → state ffi → state ffi × result γ δ) (s : state ffi) :
    is_clock_io_mono f s ∧
      (∀ s' r, f s = (s', r) → is_clock_io_mono (g r) s') ∧
      (∀ s', g (Rerr (Rabort Rtimeout_error)) s' = (s', Rerr (Rabort Rtimeout_error))) →
    is_clock_io_mono (fun s => match f s with | (s', r) => g r s') s := by
  rintro ⟨hf, hg, ht⟩
  rw [Aux.icm_iff] at hf
  have hg := hg (f s).1 (f s).2 rfl
  rw [Aux.icm_iff] at hg
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hg
  -- what happens when the first part times out
  have T : ∀ x : state ffi × result α β, x.2 = Rerr (Rabort Rtimeout_error) →
      g x.2 x.1 = (x.1, Rerr (Rabort Rtimeout_error)) := by
    intro x hx; rw [hx]; exact ht _
  have T' : ∀ x : state ffi × result α β, ¬ (g x.2 x.1).2 = Rerr (Rabort Rtimeout_error) →
      ¬ x.2 = Rerr (Rabort Rtimeout_error) := by
    intro x hx h
    rw [T x h] at hx
    exact hx rfl
  rw [Aux.icm_iff]
  show (io_events_mono s.ffi (g (f s).2 (f s).1).1.ffi ∧ _)
  refine ⟨io_events_mono_trans _ _ _ ⟨f1, g1⟩, Nat.le_trans g2 f2, Nat.le_trans f3 g3,
    Nat.le_trans f4 g4, Nat.le_trans f5 g5, fun clk => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := f6 clk
  show ((¬ (g (f { s with clock := clk }).2 (f { s with clock := clk }).1).2 = _ →
      ¬ (g (f s).2 (f s).1).2 = _ → _) ∧ (¬ (g (f s).2 (f s).1).2 = _ → _) ∧
      (¬ (g (f { s with clock := clk }).2 (f { s with clock := clk }).1).2 = _ → _) ∧ _)
  -- when neither first part times out
  have key : ¬ (f { s with clock := clk }).2 = Rerr (Rabort Rtimeout_error) →
      ¬ (f s).2 = Rerr (Rabort Rtimeout_error) →
      clk ≥ s.clock - (f s).1.clock ∧
      g (f { s with clock := clk }).2 (f { s with clock := clk }).1 =
        g (f s).2 { (f s).1 with clock := clk - (s.clock - (f s).1.clock) } := by
    intro h1 h2
    obtain ⟨b1, b2⟩ := a1 h1 h2
    exact ⟨(a2 h2).mpr h1, by rw [b1, b2]⟩
  refine ⟨fun h1 h2 => ?_, fun h2 => ⟨fun h1 => ?_, fun h1 => ?_⟩, fun h1 hc => ?_, fun hc => ?_⟩
  · obtain ⟨k1, k2⟩ := key (T' _ h1) (T' _ h2)
    obtain ⟨b1, b2, b3, b4⟩ := g6 (clk - (s.clock - (f s).1.clock))
    show (g _ _).2 = (g _ _).2 ∧ (g _ _).1 = _
    rw [k2] at h1 ⊢
    obtain ⟨c1, c2⟩ := b1 h1 h2
    refine ⟨c1, ?_⟩
    rw [c2]
    have : clk - (s.clock - (f s).1.clock) - ((f s).1.clock - (g (f s).2 (f s).1).1.clock) =
        clk - (s.clock - (g (f s).2 (f s).1).1.clock) := by omega
    rw [this]
  · have h1 : clk ≥ s.clock - (g (f s).2 (f s).1).1.clock := h1
    have n1 := (a2 (T' _ h2)).mp (by omega)
    obtain ⟨k1, k2⟩ := key n1 (T' _ h2)
    obtain ⟨b1, b2, b3, b4⟩ := g6 (clk - (s.clock - (f s).1.clock))
    show ¬ (g _ _).2 = _
    rw [k2]
    exact (b2 h2).mp (by omega)
  · obtain ⟨k1, k2⟩ := key (T' _ h1) (T' _ h2)
    obtain ⟨b1, b2, b3, b4⟩ := g6 (clk - (s.clock - (f s).1.clock))
    have h1 : ¬ (g (f { s with clock := clk }).2 (f { s with clock := clk }).1).2 = _ := h1
    rw [k2] at h1
    have := (b2 h2).mpr h1
    show clk ≥ s.clock - (g (f s).2 (f s).1).1.clock
    omega
  · have n2 := a3 (T' _ h1) hc
    obtain ⟨k1, k2⟩ := key (T' _ h1) n2
    obtain ⟨b1, b2, b3, b4⟩ := g6 (clk - (s.clock - (f s).1.clock))
    rw [k2] at h1
    exact b3 h1 (by omega)
  · show io_events_mono (g _ _).1.ffi (g _ _).1.ffi
    by_cases h1 : (f { s with clock := clk }).2 = Rerr (Rabort Rtimeout_error)
    · rw [T _ h1]
      exact io_events_mono_trans _ _ _ ⟨a4 hc, g1⟩
    · have n2 := a3 h1 hc
      obtain ⟨k1, k2⟩ := key h1 n2
      obtain ⟨b1, b2, b3, b4⟩ := g6 (clk - (s.clock - (f s).1.clock))
      rw [k2]
      exact b4 (by omega)

theorem Aux.icm_bind {α β γ δ : Type} (f : state ffi → state ffi × result α β)
    (g : result α β → state ffi → state ffi × result γ δ)
    {h : state ffi → state ffi × result γ δ} (s : state ffi)
    (H : is_clock_io_mono f s ∧
      (∀ s' r, f s = (s', r) → is_clock_io_mono (g r) s') ∧
      (∀ s', g (Rerr (Rabort Rtimeout_error)) s' = (s', Rerr (Rabort Rtimeout_error))))
    (hh : ∀ s s' r, f s = (s', r) → h s = g r s' := by
      intro s s' r hs; try dsimp only at hs
      first | rw [hs] | (dsimp only; rw [hs])
      try rfl) :
    is_clock_io_mono h s := by
  have e : h = (fun s => match f s with | (s', r) => g r s') := by
    funext s
    exact hh s _ _ rfl
  rw [e]
  exact is_clock_io_mono_bind f g s H

theorem Aux.icm_bind_val {α β γ : Type} {f : state ffi → state ffi × result α β}
    {k : α → state ffi → state ffi × result γ β}
    {h : state ffi → state ffi × result γ β} {s : state ffi}
    (h1 : is_clock_io_mono f s)
    (h2 : ∀ s' v, f s = (s', Rval v) → is_clock_io_mono (k v) s')
    (hv : ∀ s s' v, f s = (s', Rval v) → h s = k v s' := by
      intro s s' v hs; try dsimp only at hs
      first | rw [hs] | (dsimp only; rw [hs])
      try rfl)
    (he : ∀ s s' e, f s = (s', Rerr e) → h s = (s', Rerr e) := by
      intro s s' v hs; try dsimp only at hs
      first | rw [hs] | (dsimp only; rw [hs])
      try rfl) :
    is_clock_io_mono h s := by
  refine Aux.icm_bind f
    (fun r s' => match r with | Rval v => k v s' | Rerr e => (s', Rerr e)) s
    ⟨h1, fun s' r hr => ?_, fun _ => rfl⟩ (fun s s' r hr => ?_)
  · cases r with
    | Rval v => exact h2 s' v hr
    | Rerr e => exact Aux.icm_ret _ _
  · cases r with
    | Rval v => exact hv s s' v hr
    | Rerr e => exact he s s' e hr

theorem Aux.icm_ext {α β : Type} {f g : state ffi → state ffi × result α β} {s : state ffi}
    (h : ∀ s, f s = g s) (hg : is_clock_io_mono g s) : is_clock_io_mono f s := by
  have : f = g := funext h
  rw [this]
  exact hg

/-! The equations of `evaluate`, stated again so that the `match`es in them are compiled in this
file. -/

theorem Aux.evaluate_cons' (st : state ffi) (env : sem_env value) (e1 e2 : exp) (es : List exp) :
    evaluate st env (e1 :: e2 :: es) =
      match evaluate st env [e1] with
      | (st', Rval v1) =>
        match evaluate st' env (e2 :: es) with
        | (st'', Rval vs) => (st'', Rval (HD v1 :: vs))
        | (st'', Rerr v8) => (st'', Rerr v8)
      | (st', Rerr v10) => (st', Rerr v10) := by
  rw [Aux.evaluate_cons]
  rcases evaluate st env [e1] with ⟨st', v | e⟩
  · dsimp only
    rcases evaluate st' env (e2 :: es) with ⟨_, _ | _⟩ <;> rfl
  · rfl

theorem Aux.evaluate_Raise' (st : state ffi) (env : sem_env value) (e : exp) :
    evaluate st env [exp.Raise e] =
      match evaluate st env [e] with
      | (st', Rval v) => (st', Rerr (Rraise (HD v)))
      | (st', Rerr v8) => (st', Rerr v8) := by
  rw [evaluate]
  rcases evaluate st env [e] with ⟨st', v | e⟩ <;> rfl

theorem Aux.evaluate_Handle' (st : state ffi) (env : sem_env value) (e : exp)
    (pes : List (pat × exp)) :
    evaluate st env [exp.Handle e pes] =
      match evaluate st env [e] with
      | (st', r) => (fun (r : result (List value) value) (st' : state ffi) => match r with
        | Rval v7 => (st', Rval v7)
        | Rerr (Rraise v) =>
          if can_pmatch_all env.c st'.refs (pes.map Prod.fst) v then
            evaluate_match st' env v pes v
          else (st', Rerr (Rabort Rtype_error))
        | Rerr (Rabort v12) => (st', Rerr (Rabort v12))) r st' := by
  rw [Aux.evaluate_Handle]
  rcases evaluate st env [e] with ⟨st', v | e | e⟩ <;> rfl

theorem Aux.evaluate_Con' (st : state ffi) (env : sem_env value)
    (cn : Option (ident modN conN)) (es : List exp) (hc : do_con_check env.c cn es.length) :
    evaluate st env [exp.Con cn es] =
      match evaluate st env es.reverse with
      | (st', Rval vs) =>
        match build_conv env.c cn vs.reverse with
        | none => (st', Rerr (Rabort Rtype_error))
        | some v => (st', Rval [v])
      | (st', Rerr v8) => (st', Rerr v8) := by
  rw [evaluate, if_pos hc]
  rcases evaluate st env es.reverse with ⟨st', v | e⟩
  · dsimp only
    cases build_conv env.c cn v.reverse <;> rfl
  · rfl

theorem Aux.evaluate_App_FunApp (st : state ffi) (env : sem_env value) (o : op) (es : List exp)
    (ho : getOpClass o = FunApp) :
    evaluate st env [exp.App o es] =
      match evaluate st env es.reverse with
      | (st', Rval vs) =>
        match do_opapp vs.reverse with
        | some (env', e) =>
          if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error))
          else evaluate (dec_clock st') env' [e]
        | none => (st', Rerr (Rabort Rtype_error))
      | (st', Rerr e) => (st', Rerr e) := by
  rw [Aux.evaluate_App, ho]
  rcases evaluate st env es.reverse with ⟨st', vs | e⟩
  · dsimp only
    rcases do_opapp vs.reverse with _ | ⟨env', e⟩ <;> rfl
  · rfl

theorem Aux.evaluate_App_Force (st : state ffi) (env : sem_env value) (o : op) (es : List exp)
    (ho : getOpClass o = Force) :
    evaluate st env [exp.App o es] =
      match evaluate st env es.reverse with
      | (st', Rval vs) =>
        match dest_thunk vs.reverse st'.refs with
        | BadRef => (st', Rerr (Rabort Rtype_error))
        | NotThunk => (st', Rerr (Rabort Rtype_error))
        | IsThunk Evaluated v => (st', Rval [v])
        | IsThunk NotEvaluated f =>
          match do_opapp [f, Conv none []] with
          | some (env', e) =>
            if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error))
            else
              match evaluate (dec_clock st') env' [e] with
              | (st2, Rval vs2) =>
                match update_thunk vs.reverse st2.refs vs2 with
                | none => (st2, Rerr (Rabort Rtype_error))
                | some refs => ({ st2 with refs := refs }, Rval vs2)
              | (st2, Rerr e) => (st2, Rerr e)
          | none => (st', Rerr (Rabort Rtype_error))
      | (st', Rerr e) => (st', Rerr e) := by
  rw [Aux.evaluate_App, ho]
  rcases evaluate st env es.reverse with ⟨st', vs | e⟩
  · dsimp only
    rcases dest_thunk vs.reverse st'.refs with _ | _ | ⟨_ | _, f⟩
    · rfl
    · rfl
    · rfl
    · dsimp only
      rcases do_opapp [f, Conv none []] with _ | ⟨env', e⟩
      · rfl
      · dsimp only
        split
        · rfl
        · rcases evaluate (dec_clock st') env' [e] with ⟨st2, vs2 | e⟩
          · dsimp only
            cases update_thunk vs.reverse st2.refs vs2 <;> rfl
          · rfl
  · rfl

theorem Aux.evaluate_App_EvalOp (st : state ffi) (env : sem_env value) (o : op) (es : List exp)
    (ho : getOpClass o = EvalOp) :
    evaluate st env [exp.App o es] =
      match evaluate st env es.reverse with
      | (st', Rval vs) =>
        match do_eval_res vs.reverse st' with
        | (st1, Rval p) =>
          if st1.clock = 0 then (st1, Rerr (Rabort Rtimeout_error))
          else
            match evaluate_decs (dec_clock st1) p.1 p.2 with
            | (st2, r) =>
              (fun (r : result (sem_env value) value) (st2 : state ffi) =>
                (match r with
                | Rval env2 =>
                  match declare_env st2.eval_state (extend_dec_env env2 p.1) with
                  | some (x, es2) =>
                    ({ st2 with eval_state := reset_env_generation st'.eval_state es2 }, Rval [x])
                  | none => (st2, Rerr (Rabort Rtype_error))
                | Rerr (Rabort a) => (st2, Rerr (Rabort a))
                | Rerr e =>
                  ({ st2 with
                      eval_state := reset_env_generation st'.eval_state st2.eval_state },
                    Rerr e) : state ffi × result (List value) value)) r st2
        | (st1, Rerr e) => (st1, Rerr e)
      | (st', Rerr e) => (st', Rerr e) := by
  rw [Aux.evaluate_App, ho]
  rcases evaluate st env es.reverse with ⟨st', vs | e⟩
  · dsimp only
    rcases (do_eval_res vs.reverse st' : state ffi × result _ value) with
      ⟨st1, ⟨env1, decs⟩ | e⟩
    · dsimp only
      split
      · rfl
      · rcases evaluate_decs (dec_clock st1) env1 decs with ⟨st2, env2 | e | e⟩
        · dsimp only
          rcases declare_env st2.eval_state (extend_dec_env env2 env1) with _ | ⟨x, es2⟩ <;> rfl
        · rfl
        · rfl
    · rfl
  · rfl

theorem Aux.evaluate_Log' (st : state ffi) (env : sem_env value) (l : lop) (e1 e2 : exp) :
    evaluate st env [exp.Log l e1 e2] =
      match evaluate st env [e1] with
      | (st', Rval v1) =>
        match do_log l (HD v1) e2 with
        | none => (st', Rerr (Rabort Rtype_error))
        | some (Exp e) => evaluate st' env [e]
        | some (Val v) => (st', Rval [v])
      | (st', Rerr v9) => (st', Rerr v9) := by
  rw [Aux.evaluate_Log]
  rcases evaluate st env [e1] with ⟨st', vs | e⟩
  · dsimp only
    rcases do_log l (HD vs) e2 with _ | _ | _ <;> rfl
  · rfl

theorem Aux.evaluate_If' (st : state ffi) (env : sem_env value) (e1 e2 e3 : exp) :
    evaluate st env [exp.If e1 e2 e3] =
      match evaluate st env [e1] with
      | (st', Rval v) =>
        match do_if (HD v) e2 e3 with
        | none => (st', Rerr (Rabort Rtype_error))
        | some e => evaluate st' env [e]
      | (st', Rerr v8) => (st', Rerr v8) := by
  rw [Aux.evaluate_If]
  rcases evaluate st env [e1] with ⟨st', vs | e⟩
  · dsimp only
    cases do_if (HD vs) e2 e3 <;> rfl
  · rfl

theorem Aux.evaluate_Mat' (st : state ffi) (env : sem_env value) (e : exp)
    (pes : List (pat × exp)) :
    evaluate st env [exp.Mat e pes] =
      match evaluate st env [e] with
      | (st', Rval v) =>
        if can_pmatch_all env.c st'.refs (pes.map Prod.fst) (HD v) then
          evaluate_match st' env (HD v) pes bind_exn_v
        else (st', Rerr (Rabort Rtype_error))
      | (st', Rerr v8) => (st', Rerr v8) := by
  rw [Aux.evaluate_Mat]
  rcases evaluate st env [e] with ⟨st', vs | e⟩ <;> rfl

theorem Aux.evaluate_Let' (st : state ffi) (env : sem_env value) (xo : Option varN)
    (e1 e2 : exp) :
    evaluate st env [exp.Let xo e1 e2] =
      match evaluate st env [e1] with
      | (st', Rval v) => evaluate st' { env with v := nsOptBind xo (HD v) env.v } [e2]
      | (st', Rerr v8) => (st', Rerr v8) := by
  rw [Aux.evaluate_Let]
  rcases evaluate st env [e1] with ⟨st', vs | e⟩ <;> rfl

theorem Aux.evaluate_decs_cons' (st : state ffi) (env : sem_env value) (d1 d2 : dec)
    (ds : List dec) :
    evaluate_decs st env (d1 :: d2 :: ds) =
      match evaluate_decs st env [d1] with
      | (st1, Rval env1) =>
        match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds) with
        | (st2, r) => (st2, combine_dec_result env1 r)
      | (st1, Rerr v7) => (st1, Rerr v7) := by
  rw [Aux.evaluate_decs_cons]
  rcases evaluate_decs st env [d1] with ⟨st', vs | e⟩ <;> rfl

theorem Aux.evaluate_Dlet' (st : state ffi) (env : sem_env value) (l : locs) (p : pat) (e : exp)
    (hc : ALL_DISTINCT (pat_bindings p []) ∧ every_exp (one_con_check env.c) e) :
    evaluate_decs st env [Dlet l p e] =
      match evaluate st env [e] with
      | (st', Rval v) =>
        (st',
          match pmatch env.c st'.refs p (HD v) [] with
          | No_match => Rerr (Rraise bind_exn_v)
          | Match_type_error => Rerr (Rabort Rtype_error)
          | Match new_vals => Rval { v := alist_to_ns new_vals, c := nsEmpty })
      | (st', Rerr err) => (st', Rerr err) := by
  rw [evaluate_decs, if_pos hc]
  rcases evaluate st env [e] with ⟨st', vs | e⟩
  · dsimp only
    cases pmatch env.c st'.refs p (HD vs) [] <;> rfl
  · rfl

theorem Aux.evaluate_Dmod' (st : state ffi) (env : sem_env value) (mn : modN) (ds : List dec) :
    evaluate_decs st env [Dmod mn ds] =
      match evaluate_decs st env ds with
      | (st', r) =>
        (st',
          match r with
          | Rval env' => Rval { v := nsLift mn env'.v, c := nsLift mn env'.c }
          | Rerr err => Rerr err) := by
  rw [evaluate_decs]
  rcases evaluate_decs st env ds with ⟨st', vs | e⟩ <;> rfl

theorem Aux.evaluate_Dlocal' (st : state ffi) (env : sem_env value) (lds ds : List dec) :
    evaluate_decs st env [Dlocal lds ds] =
      match evaluate_decs st env lds with
      | (st1, Rval env1) => evaluate_decs st1 (extend_dec_env env1 env) ds
      | (st1, Rerr v7) => (st1, Rerr v7) := by
  rw [Aux.evaluate_Dlocal]
  rcases evaluate_decs st env lds with ⟨st', vs | e⟩ <;> rfl

theorem Aux.icm_clock {α β : Type} {f : state ffi → state ffi × result α β} {s s' : state ffi}
    {r : result α β} (h : is_clock_io_mono f s) (hf : f s = (s', r)) : s'.clock ≤ s.clock := by
  have := ((Aux.icm_iff f s).mp h).2.1
  rw [hf] at this
  exact this

/- HOL4:
Theorem is_clock_io_mono_check:
   (~ (s.clock = 0) ==>
        is_clock_io_mono (\s. f (adj_clock 1 0 s)) (dec_clock s))
    ==> is_clock_io_mono (\s. if s.clock = 0
        then (s,Rerr (Rabort Rtimeout_error)) else f s) s -/
theorem is_clock_io_mono_check {α β : Type} (f : state ffi → state ffi × result α β)
    (s : state ffi) :
    (¬ (s.clock = 0) → is_clock_io_mono (fun s => f (adj_clock 1 0 s)) (dec_clock s)) →
    is_clock_io_mono
      (fun s => if s.clock = 0 then (s, Rerr (Rabort Rtimeout_error)) else f s) s := by
  intro h
  rw [Aux.icm_iff]
  dsimp only
  by_cases h0 : s.clock = 0
  · rw [if_pos h0]
    refine ⟨io_events_mono_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      fun clk => ⟨fun _ h2 => absurd rfl h2, fun h2 => absurd rfl h2, fun h1 hc => ?_,
        fun hc => ?_⟩⟩
    · rw [if_pos (by omega)] at h1
      exact absurd rfl h1
    · rw [if_pos (by omega)]
      exact io_events_mono_refl _
  · rw [if_neg h0]
    have h := (Aux.icm_iff _ _).mp (h h0)
    dsimp only at h
    have e : adj_clock 1 0 (dec_clock s) = s := by
      cases s
      simp only [adj_clock, dec_clock] at h0 ⊢
      congr 1
      omega
    rw [e] at h
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
    have a2 : (f s).1.clock ≤ s.clock - 1 := a2
    refine ⟨a1, by omega, a3, a4, a5, fun clk => ?_⟩
    cases clk with
    | zero =>
      rw [if_pos rfl]
      refine ⟨fun h1 _ => absurd rfl h1, fun h2 => ⟨fun h1 => by omega, fun h1 => absurd rfl h1⟩,
        fun h1 => absurd rfl h1, fun _ => a1⟩
    | succ k =>
      rw [if_neg (Nat.succ_ne_zero k)]
      have e2 : adj_clock 1 0 { dec_clock s with clock := k } = { s with clock := k + 1 } := rfl
      have b := a6 k
      rw [e2] at b
      have e3 : (dec_clock s).clock = s.clock - 1 := rfl
      rw [e3] at b
      obtain ⟨b1, b2, b3, b4⟩ := b
      refine ⟨fun h1 h2 => ?_, fun h2 => ?_, fun h1 hc => b3 h1 (by omega),
        fun hc => b4 (by omega)⟩
      · obtain ⟨c1, c2⟩ := b1 h1 h2
        refine ⟨c1, ?_⟩
        rw [c2]
        have : k - (s.clock - 1 - (f s).1.clock) = k + 1 - (s.clock - (f s).1.clock) := by omega
        rw [this]
      · rw [← b2 h2]
        omega

/- HOL4:
Theorem dec_inc_clock:
  dec_clock (adj_clock 1 0 s) = s -/
theorem dec_inc_clock (s : state ffi) : dec_clock (adj_clock 1 0 s) = s := by
  cases s
  simp [dec_clock, adj_clock]

/- HOL4:
Theorem do_app_refs_length:
   do_app refs_ffi op vs = SOME res ==>
   LENGTH (FST refs_ffi) <= LENGTH (FST (FST res)) -/
theorem do_app_refs_length (refs_ffi : List (store_v value) × ffi_state ffi) (op : CmlTS.op)
    (vs : List value) (res : (List (store_v value) × ffi_state ffi) × result value value) :
    do_app refs_ffi op vs = some res → refs_ffi.1.length ≤ res.1.1.length := by
  obtain ⟨s, t⟩ := refs_ffi
  obtain ⟨st', v⟩ := res
  intro h
  exact (Aux.do_app_facts h).1

/- HOL4:
Theorem is_clock_io_mono_do_app_simple:
  ! xs (st:'ffi state).
   is_clock_io_mono (\st'.
    case do_app (st'.refs, st'.ffi) op xs of
      NONE => (st', Rerr (Rabort Rtype_error))
    | SOME ((refs,ffi),r) =>
      (st' with<| refs := refs; ffi := ffi |>, list_result r)) st -/
theorem is_clock_io_mono_do_app_simple (op : CmlTS.op) :
    ∀ (xs : List value) (st : state ffi),
      is_clock_io_mono (fun st' : state ffi =>
        match do_app (st'.refs, st'.ffi) op xs with
        | none => (st', Rerr (Rabort Rtype_error))
        | some ((refs, ffi), r) => ({ st' with refs := refs, ffi := ffi }, list_result r)) st := by
  intro xs st
  cases h : do_app (st.refs, st.ffi) op xs with
  | none =>
    refine Aux.icm_noclock (s' := st) (r := Rerr (Rabort Rtype_error)) (fun clk => ?_)
      (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    simp only [h]
  | some x =>
    obtain ⟨⟨refs, ffi'⟩, r⟩ := x
    refine Aux.icm_noclock (s' := { st with refs := refs, ffi := ffi' }) (r := list_result r)
      (fun clk => ?_) (do_app_io_events_mono _ _ _ _ _ _ _ h) (Nat.le_refl _) (Nat.le_refl _)
      (do_app_refs_length _ _ _ _ h)
    simp only [h]

theorem Aux.evaluate_App_Simple (st : state ffi) (env : sem_env value) (o : op) (es : List exp)
    (ho : getOpClass o = Simple) :
    evaluate st env [exp.App o es] =
      match evaluate st env es.reverse with
      | (st', Rval vs) =>
        match do_app (st'.refs, st'.ffi) o vs.reverse with
        | none => (st', Rerr (Rabort Rtype_error))
        | some ((refs, ffi), r) => ({ st' with refs := refs, ffi := ffi }, list_result r)
      | (st', Rerr e) => (st', Rerr e) := by
  rw [Aux.evaluate_App, ho]
  rcases evaluate st env es.reverse with ⟨st', vs | e⟩
  · dsimp only
    rcases do_app (st'.refs, st'.ffi) o vs.reverse with _ | ⟨⟨refs, ffi'⟩, r⟩ <;> rfl
  · rfl

/- HOL4:
Theorem is_clock_io_mono_evaluate:
   (!(s : 'ffi state) env es. is_clock_io_mono (\s. evaluate s env es) s) /\
   (!(s : 'ffi state) env v pes err_v.
        is_clock_io_mono (\s. evaluate_match s env v pes err_v) s) /\
   (!(s : 'ffi state) env ds.
        is_clock_io_mono (\s. evaluate_decs s env ds) s) -/
theorem is_clock_io_mono_evaluate :
    (∀ (s : state ffi) (env : sem_env value) (es : List exp),
      is_clock_io_mono (fun s => evaluate s env es) s) ∧
    (∀ (s : state ffi) (env : sem_env value) (v : value) (pes : List (pat × exp))
      (err_v : value),
      is_clock_io_mono (fun s => evaluate_match s env v pes err_v) s) ∧
    (∀ (s : state ffi) (env : sem_env value) (ds : List dec),
      is_clock_io_mono (fun s => evaluate_decs s env ds) s) := by
  refine Aux.eval_induct
    (P := fun st env es => is_clock_io_mono (fun s => evaluate s env es) st)
    (Q := fun st env v pes err => is_clock_io_mono (fun s => evaluate_match s env v pes err) st)
    (D := fun st env ds => is_clock_io_mono (fun s => evaluate_decs s env ds) st)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro st env
    simp only [evaluate]
    exact Aux.icm_ret _ _
  · intro st env e1 e2 es ih1 ih2
    refine Aux.icm_ext (fun s => Aux.evaluate_cons' s env e1 e2 es) ?_
    refine Aux.icm_bind_val (f := fun s => evaluate s env [e1])
      (k := fun v1 s => match evaluate s env (e2 :: es) with
        | (st'', Rval vs) => (st'', Rval (HD v1 :: vs))
        | (st'', Rerr v8) => (st'', Rerr v8)) ih1 (fun s' v hs => ?_)
    exact Aux.icm_bind_val (f := fun s => evaluate s env (e2 :: es))
      (k := fun vs s => (s, Rval (HD v :: vs))) (ih2 s' (Aux.icm_clock ih1 hs))
      (fun s' v' _ => Aux.icm_ret _ _)
  · intro st env l
    simp only [evaluate]
    exact Aux.icm_ret _ _
  · intro st env e ih
    refine Aux.icm_ext (fun s => Aux.evaluate_Raise' s env e) ?_
    exact Aux.icm_bind_val (f := fun s => evaluate s env [e])
      (k := fun v s => (s, Rerr (Rraise (HD v)))) ih (fun s' v' _ => Aux.icm_ret _ _)
  · intro st env e pes ih1 ih2
    refine Aux.icm_ext (fun s => Aux.evaluate_Handle' s env e pes) ?_
    refine Aux.icm_bind (fun s => evaluate s env [e])
      (fun (r : result (List value) value) (st' : state ffi) => match r with
        | Rval v7 => (st', Rval v7)
        | Rerr (Rraise v) =>
          if can_pmatch_all env.c st'.refs (pes.map Prod.fst) v then
            evaluate_match st' env v pes v
          else (st', Rerr (Rabort Rtype_error))
        | Rerr (Rabort v12) => (st', Rerr (Rabort v12))) st ⟨ih1, fun s' r hr => ?_,
      fun _ => rfl⟩
    rcases r with v | v | a
    · exact Aux.icm_ret _ _
    · dsimp only
      by_cases hc : can_pmatch_all env.c s'.refs (pes.map Prod.fst) v
      · refine (is_clock_io_mono_cong s' s' _ (fun s => evaluate_match s env v pes v) rfl
          (fun s hs => ?_)).mpr (ih2 s' v (Aux.icm_clock ih1 hr))
        rw [hs.2.1, if_pos hc]
      · refine (is_clock_io_mono_cong s' s' _ (fun s => (s, Rerr (Rabort Rtype_error))) rfl
          (fun s hs => ?_)).mpr (Aux.icm_ret _ _)
        rw [hs.2.1, if_neg hc]
    · exact Aux.icm_ret _ _
  · intro st env cn es ih
    by_cases hc : do_con_check env.c cn es.length
    · refine Aux.icm_ext (fun s => Aux.evaluate_Con' s env cn es hc) ?_
      refine Aux.icm_bind_val (f := fun s => evaluate s env es.reverse)
        (k := fun vs s => match build_conv env.c cn vs.reverse with
          | none => (s, Rerr (Rabort Rtype_error))
          | some v => (s, Rval [v])) ih (fun s' v' _ => ?_)
      dsimp only
      cases build_conv env.c cn v'.reverse <;> exact Aux.icm_ret _ _
    · simp only [evaluate, if_neg hc]
      exact Aux.icm_ret _ _
  · intro st env n
    simp only [evaluate]
    cases nsLookup env.v n <;> exact Aux.icm_ret _ _
  · intro st env x e
    simp only [evaluate]
    exact Aux.icm_ret _ _
  · intro st env o es ih1 ih2 ih3
    cases ho : getOpClass o with
    | FunApp =>
      refine Aux.icm_ext (fun s => Aux.evaluate_App_FunApp s env o es ho) ?_
      refine Aux.icm_bind_val (f := fun s => evaluate s env es.reverse)
        (k := fun vs st' => match do_opapp vs.reverse with
          | some (env', e) =>
            if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error))
            else evaluate (dec_clock st') env' [e]
          | none => (st', Rerr (Rabort Rtype_error))) ih1 (fun s' vs hs => ?_)
      have hcl := Aux.icm_clock ih1 hs
      dsimp only
      rcases do_opapp vs.reverse with _ | ⟨env', e⟩
      · exact Aux.icm_ret _ _
      · dsimp only
        refine is_clock_io_mono_check (fun s => evaluate (dec_clock s) env' [e]) s' (fun h0 => ?_)
        simp only [dec_inc_clock]
        exact ih2 _ _ _ (by simp only [dec_clock]; omega)
    | Force =>
      refine Aux.icm_ext (fun s => Aux.evaluate_App_Force s env o es ho) ?_
      refine Aux.icm_bind_val (f := fun s => evaluate s env es.reverse)
        (k := fun vs st' => match dest_thunk vs.reverse st'.refs with
          | BadRef => (st', Rerr (Rabort Rtype_error))
          | NotThunk => (st', Rerr (Rabort Rtype_error))
          | IsThunk Evaluated v => (st', Rval [v])
          | IsThunk NotEvaluated f =>
            match do_opapp [f, Conv none []] with
            | some (env', e) =>
              if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error))
              else
                match evaluate (dec_clock st') env' [e] with
                | (st2, Rval vs2) =>
                  match update_thunk vs.reverse st2.refs vs2 with
                  | none => (st2, Rerr (Rabort Rtype_error))
                  | some refs => ({ st2 with refs := refs }, Rval vs2)
                | (st2, Rerr e) => (st2, Rerr e)
            | none => (st', Rerr (Rabort Rtype_error))) ih1 (fun s' vs hs => ?_)
      have hcl := Aux.icm_clock ih1 hs
      dsimp only
      refine (is_clock_io_mono_cong s' s' _ (fun st' => match dest_thunk vs.reverse s'.refs with
          | BadRef => (st', Rerr (Rabort Rtype_error))
          | NotThunk => (st', Rerr (Rabort Rtype_error))
          | IsThunk Evaluated v => (st', Rval [v])
          | IsThunk NotEvaluated f =>
            match do_opapp [f, Conv none []] with
            | some (env', e) =>
              if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error))
              else
                match evaluate (dec_clock st') env' [e] with
                | (st2, Rval vs2) =>
                  match update_thunk vs.reverse st2.refs vs2 with
                  | none => (st2, Rerr (Rabort Rtype_error))
                  | some refs => ({ st2 with refs := refs }, Rval vs2)
                | (st2, Rerr e) => (st2, Rerr e)
            | none => (st', Rerr (Rabort Rtype_error))) rfl
          (fun s hs => by rw [hs.2.1])).mpr ?_
      rcases dest_thunk vs.reverse s'.refs with _ | _ | ⟨m, f⟩
      · exact Aux.icm_ret _ _
      · exact Aux.icm_ret _ _
      · cases m with
        | Evaluated => exact Aux.icm_ret _ _
        | NotEvaluated =>
          dsimp only
          rcases do_opapp [f, Conv none []] with _ | ⟨env', e⟩
          · exact Aux.icm_ret _ _
          · refine is_clock_io_mono_check (fun s => match evaluate (dec_clock s) env' [e] with
                | (st2, Rval vs2) =>
                  match update_thunk vs.reverse st2.refs vs2 with
                  | none => (st2, Rerr (Rabort Rtype_error))
                  | some refs => ({ st2 with refs := refs }, Rval vs2)
                | (st2, Rerr e) => (st2, Rerr e)) s' (fun h0 => ?_)
            simp only [dec_inc_clock]
            refine Aux.icm_bind_val (f := fun s => evaluate s env' [e])
              (k := fun vs2 st2 => match update_thunk vs.reverse st2.refs vs2 with
                | none => (st2, Rerr (Rabort Rtype_error))
                | some refs => ({ st2 with refs := refs }, Rval vs2))
              (ih2 _ _ _ (by simp only [dec_clock]; omega)) (fun s2 vs2 _ => ?_)
            dsimp only
            cases hu : update_thunk vs.reverse s2.refs vs2 with
            | none =>
              refine Aux.icm_noclock (s' := s2) (r := Rerr (Rabort Rtype_error))
                (fun clk => ?_) (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _)
                (Nat.le_refl _)
              simp only [hu]
            | some refs =>
              have hl : refs.length = s2.refs.length := by
                unfold update_thunk at hu
                split at hu
                · split at hu
                  · exact Aux.store_assign_length hu
                  · cases hu
                · cases hu
              refine Aux.icm_noclock (s' := { s2 with refs := refs }) (r := Rval vs2)
                (fun clk => ?_) (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _)
                (Nat.le_of_eq hl.symm)
              simp only [hu]
    | EvalOp =>
      refine Aux.icm_ext (fun s => Aux.evaluate_App_EvalOp s env o es ho) ?_
      refine Aux.icm_bind_val (f := fun s => evaluate s env es.reverse)
        (k := fun vs st' => match do_eval_res vs.reverse st' with
          | (st1, Rval p) =>
            if st1.clock = 0 then (st1, Rerr (Rabort Rtimeout_error))
            else
              match evaluate_decs (dec_clock st1) p.1 p.2 with
              | (st2, r) =>
                (fun (r : result (sem_env value) value) (st2 : state ffi) =>
                  (match r with
                  | Rval env2 =>
                    match declare_env st2.eval_state (extend_dec_env env2 p.1) with
                    | some (x, es2) =>
                      ({ st2 with eval_state := reset_env_generation st'.eval_state es2 },
                        Rval [x])
                    | none => (st2, Rerr (Rabort Rtype_error))
                  | Rerr (Rabort a) => (st2, Rerr (Rabort a))
                  | Rerr e =>
                    ({ st2 with
                        eval_state := reset_env_generation st'.eval_state st2.eval_state },
                      Rerr e) : state ffi × result (List value) value)) r st2
          | (st1, Rerr e) => (st1, Rerr e)) ih1 (fun s' vs hs => ?_)
      have hcl := Aux.icm_clock ih1 hs
      dsimp only
      refine (is_clock_io_mono_cong s' s' _ (fun st' => match do_eval_res vs.reverse st' with
          | (st1, Rval p) =>
            if st1.clock = 0 then (st1, Rerr (Rabort Rtimeout_error))
            else
              match evaluate_decs (dec_clock st1) p.1 p.2 with
              | (st2, r) =>
                (fun (r : result (sem_env value) value) (st2 : state ffi) =>
                  (match r with
                  | Rval env2 =>
                    match declare_env st2.eval_state (extend_dec_env env2 p.1) with
                    | some (x, es2) =>
                      ({ st2 with eval_state := reset_env_generation s'.eval_state es2 },
                        Rval [x])
                    | none => (st2, Rerr (Rabort Rtype_error))
                  | Rerr (Rabort a) => (st2, Rerr (Rabort a))
                  | Rerr e =>
                    ({ st2 with
                        eval_state := reset_env_generation s'.eval_state st2.eval_state },
                      Rerr e) : state ffi × result (List value) value)) r st2
          | (st1, Rerr e) => (st1, Rerr e)) rfl (fun s hs => by rw [hs.1])).mpr ?_
      have hE : is_clock_io_mono (fun st' : state ffi =>
          (do_eval_res vs.reverse st' :
            state ffi × result (sem_env value × List dec) value)) s' := by
        cases hd : do_eval vs.reverse s'.eval_state with
        | none =>
          refine Aux.icm_noclock (s' := s') (r := Rerr (Rabort Rtype_error))
            (fun clk => ?_) (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _)
            (Nat.le_refl _)
          simp only [do_eval_res, hd]
        | some x =>
          obtain ⟨env1, decs, es1⟩ := x
          refine Aux.icm_noclock (s' := { s' with eval_state := es1 }) (r := Rval (env1, decs))
            (fun clk => ?_) (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _)
            (Nat.le_refl _)
          simp only [do_eval_res, hd]
      refine Aux.icm_bind_val
        (f := fun st' => (do_eval_res vs.reverse st' :
            state ffi × result (sem_env value × List dec) value))
        (k := fun p st1 =>
            if st1.clock = 0 then (st1, Rerr (Rabort Rtimeout_error))
            else
              match evaluate_decs (dec_clock st1) p.1 p.2 with
              | (st2, r) =>
                (fun (r : result (sem_env value) value) (st2 : state ffi) =>
                  (match r with
                  | Rval env2 =>
                    match declare_env st2.eval_state (extend_dec_env env2 p.1) with
                    | some (x, es2) =>
                      ({ st2 with eval_state := reset_env_generation s'.eval_state es2 },
                        Rval [x])
                    | none => (st2, Rerr (Rabort Rtype_error))
                  | Rerr (Rabort a) => (st2, Rerr (Rabort a))
                  | Rerr e =>
                    ({ st2 with
                        eval_state := reset_env_generation s'.eval_state st2.eval_state },
                      Rerr e) : state ffi × result (List value) value)) r st2)
        hE (fun st1 p hp => ?_)
      have hcl2 := Aux.icm_clock hE hp
      obtain ⟨env1, decs⟩ := p
      dsimp only
      refine is_clock_io_mono_check (fun st1 =>
              match evaluate_decs (dec_clock st1) env1 decs with
              | (st2, r) =>
                (fun (r : result (sem_env value) value) (st2 : state ffi) =>
                  (match r with
                  | Rval env2 =>
                    match declare_env st2.eval_state (extend_dec_env env2 env1) with
                    | some (x, es2) =>
                      ({ st2 with eval_state := reset_env_generation s'.eval_state es2 },
                        Rval [x])
                    | none => (st2, Rerr (Rabort Rtype_error))
                  | Rerr (Rabort a) => (st2, Rerr (Rabort a))
                  | Rerr e =>
                    ({ st2 with
                        eval_state := reset_env_generation s'.eval_state st2.eval_state },
                      Rerr e) : state ffi × result (List value) value)) r st2)
        st1 (fun h0 => ?_)
      refine Aux.icm_bind (fun s => evaluate_decs s env1 decs)
        (fun (r : result (sem_env value) value) (st2 : state ffi) =>
                  (match r with
                  | Rval env2 =>
                    match declare_env st2.eval_state (extend_dec_env env2 env1) with
                    | some (x, es2) =>
                      ({ st2 with eval_state := reset_env_generation s'.eval_state es2 },
                        Rval [x])
                    | none => (st2, Rerr (Rabort Rtype_error))
                  | Rerr (Rabort a) => (st2, Rerr (Rabort a))
                  | Rerr e =>
                    ({ st2 with
                        eval_state := reset_env_generation s'.eval_state st2.eval_state },
                      Rerr e) : state ffi × result (List value) value)) _
        ⟨ih3 _ _ _ (by simp only [dec_clock]; omega), fun s2 r hr => ?_, fun _ => rfl⟩
        (fun s s3 r hr => by
          rw [← dec_inc_clock s] at hr
          dsimp only at hr ⊢
          rw [hr])
      rcases r with v | v | a
      · cases hd : declare_env s2.eval_state (extend_dec_env v env1) with
        | none =>
          refine Aux.icm_noclock (s' := s2) (r := Rerr (Rabort Rtype_error))
            (fun clk => ?_) (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _)
            (Nat.le_refl _)
          simp only [hd]
        | some x =>
          obtain ⟨x, es2⟩ := x
          refine Aux.icm_noclock
            (s' := { s2 with eval_state := reset_env_generation s'.eval_state es2 })
            (r := Rval [x])
            (fun clk => ?_) (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _)
            (Nat.le_refl _)
          simp only [hd]
      · exact Aux.icm_noclock
          (s' := { s2 with eval_state := reset_env_generation s'.eval_state s2.eval_state })
          (r := Rerr (Rraise v)) (fun clk => rfl) (io_events_mono_refl _) (Nat.le_refl _)
          (Nat.le_refl _) (Nat.le_refl _)
      · exact Aux.icm_ret _ _
    | Simple =>
      refine Aux.icm_ext (fun s => Aux.evaluate_App_Simple s env o es ho) ?_
      refine Aux.icm_bind_val (f := fun s => evaluate s env es.reverse)
        (k := fun vs st' => match do_app (st'.refs, st'.ffi) o vs.reverse with
          | none => (st', Rerr (Rabort Rtype_error))
          | some ((refs, ffi), r) => ({ st' with refs := refs, ffi := ffi }, list_result r))
        ih1 (fun s' vs hs => ?_)
      exact is_clock_io_mono_do_app_simple o vs.reverse s'
  · intro st env l e1 e2 ih1 ih2
    refine Aux.icm_ext (fun s => Aux.evaluate_Log' s env l e1 e2) ?_
    refine Aux.icm_bind_val (f := fun s => evaluate s env [e1])
      (k := fun v1 st' => match do_log l (HD v1) e2 with
        | none => (st', Rerr (Rabort Rtype_error))
        | some (Exp e) => evaluate st' env [e]
        | some (Val v) => (st', Rval [v])) ih1 (fun s' v hs => ?_)
    dsimp only
    cases hl : do_log l (HD v) e2 with
    | none => exact Aux.icm_ret _ _
    | some x =>
      cases x with
      | Exp e =>
        dsimp only
        rw [do_log_exp_aux hl]
        exact ih2 s' (Aux.icm_clock ih1 hs)
      | Val v => exact Aux.icm_ret _ _
  · intro st env e1 e2 e3 ih1 ih2 ih3
    refine Aux.icm_ext (fun s => Aux.evaluate_If' s env e1 e2 e3) ?_
    refine Aux.icm_bind_val (f := fun s => evaluate s env [e1])
      (k := fun v1 st' => match do_if (HD v1) e2 e3 with
        | none => (st', Rerr (Rabort Rtype_error))
        | some e => evaluate st' env [e]) ih1 (fun s' v hs => ?_)
    have hcl := Aux.icm_clock ih1 hs
    dsimp only
    cases hl : do_if (HD v) e2 e3 with
    | none => exact Aux.icm_ret _ _
    | some e' =>
      dsimp only
      unfold do_if at hl
      split at hl
      · cases hl; exact ih2 s' hcl
      · split at hl
        · cases hl; exact ih3 s' hcl
        · cases hl
  · intro st env e pes ih1 ih2
    refine Aux.icm_ext (fun s => Aux.evaluate_Mat' s env e pes) ?_
    refine Aux.icm_bind_val (f := fun s => evaluate s env [e])
      (k := fun v st' => if can_pmatch_all env.c st'.refs (pes.map Prod.fst) (HD v) then
          evaluate_match st' env (HD v) pes bind_exn_v
        else (st', Rerr (Rabort Rtype_error))) ih1 (fun s' v hs => ?_)
    dsimp only
    by_cases hc : can_pmatch_all env.c s'.refs (pes.map Prod.fst) (HD v)
    · refine (is_clock_io_mono_cong s' s' _ (fun s => evaluate_match s env (HD v) pes bind_exn_v)
        rfl (fun s hs => ?_)).mpr (ih2 s' (HD v) (Aux.icm_clock ih1 hs))
      rw [hs.2.1, if_pos hc]
    · refine (is_clock_io_mono_cong s' s' _ (fun s => (s, Rerr (Rabort Rtype_error))) rfl
        (fun s hs => ?_)).mpr (Aux.icm_ret _ _)
      rw [hs.2.1, if_neg hc]
  · intro st env xo e1 e2 ih1 ih2
    refine Aux.icm_ext (fun s => Aux.evaluate_Let' s env xo e1 e2) ?_
    exact Aux.icm_bind_val (f := fun s => evaluate s env [e1])
      (k := fun v st' => evaluate st' { env with v := nsOptBind xo (HD v) env.v } [e2]) ih1
      (fun s' v hs => ih2 s' _ (Aux.icm_clock ih1 hs))
  · intro st env funs e ih
    simp only [evaluate]
    by_cases hc : ALL_DISTINCT (funs.map (fun (x, _, _) => x))
    · simp only [if_pos hc]
      exact ih _
    · simp only [if_neg hc]
      exact Aux.icm_ret _ _
  · intro st env e t ih
    simp only [evaluate]
    exact ih
  · intro st env e l ih
    simp only [evaluate]
    exact ih
  · intro st env v err
    simp only [evaluate_match]
    exact Aux.icm_ret _ _
  · intro st env v p e pes err ih1 ih2
    simp only [evaluate_match]
    by_cases hc : ALL_DISTINCT (pat_bindings p [])
    · simp only [if_pos hc]
      cases hm : pmatch env.c st.refs p v [] with
      | No_match =>
        refine (is_clock_io_mono_cong st st _ (fun s => evaluate_match s env v pes err) rfl
          (fun s hs => ?_)).mpr ih1
        rw [hs.2.1, hm]
      | Match_type_error =>
        refine (is_clock_io_mono_cong st st _ (fun s => (s, Rerr (Rabort Rtype_error))) rfl
          (fun s hs => ?_)).mpr (Aux.icm_ret _ _)
        rw [hs.2.1, hm]
      | Match env_v' =>
        refine (is_clock_io_mono_cong st st _ (fun s =>
          evaluate s { env with v := nsAppend (alist_to_ns env_v') env.v } [e]) rfl
          (fun s hs => ?_)).mpr (ih2 _)
        rw [hs.2.1, hm]
    · simp only [if_neg hc]
      exact Aux.icm_ret _ _
  · intro st env
    simp only [evaluate_decs]
    exact Aux.icm_ret _ _
  · intro st env d1 d2 ds ih1 ih2
    refine Aux.icm_ext (fun s => Aux.evaluate_decs_cons' s env d1 d2 ds) ?_
    refine Aux.icm_bind_val (f := fun s => evaluate_decs s env [d1])
      (k := fun env1 st1 => match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds) with
        | (st2, r) => (st2, combine_dec_result env1 r)) ih1 (fun s' v hs => ?_)
    exact Aux.icm_bind (fun s => evaluate_decs s (extend_dec_env v env) (d2 :: ds))
      (fun r st2 => (st2, combine_dec_result v r)) s'
      ⟨ih2 s' _ (Aux.icm_clock ih1 hs), fun _ _ _ => Aux.icm_ret _ _, fun _ => rfl⟩
  · intro st env l p e ih
    by_cases hc : ALL_DISTINCT (pat_bindings p []) ∧ every_exp (one_con_check env.c) e
    · refine Aux.icm_ext (fun s => Aux.evaluate_Dlet' s env l p e hc) ?_
      refine Aux.icm_bind_val (f := fun s => evaluate s env [e])
        (k := fun v st' => (st', match pmatch env.c st'.refs p (HD v) [] with
            | No_match => Rerr (Rraise bind_exn_v)
            | Match_type_error => Rerr (Rabort Rtype_error)
            | Match new_vals =>
              Rval ({ v := alist_to_ns new_vals, c := nsEmpty } : sem_env value))) ih
        (fun s' v hs => ?_)
      dsimp only
      refine (is_clock_io_mono_cong s' s' _
        (fun s => (s, match pmatch env.c s'.refs p (HD v) [] with
            | No_match => Rerr (Rraise bind_exn_v)
            | Match_type_error => Rerr (Rabort Rtype_error)
            | Match new_vals =>
              Rval ({ v := alist_to_ns new_vals, c := nsEmpty } : sem_env value))) rfl
          (fun s hs => ?_)).mpr (Aux.icm_ret _ _)
      rw [hs.2.1]
    · simp only [evaluate_decs, if_neg hc]
      exact Aux.icm_ret _ _
  · intro st env l funs
    simp only [evaluate_decs]
    exact Aux.icm_ret _ _
  · intro st env l tds
    simp only [evaluate_decs]
    by_cases hc : EVERY check_dup_ctors tds
    · simp only [if_pos hc]
      exact Aux.icm_noclock
        (s' := { st with next_type_stamp := st.next_type_stamp + tds.length })
        (r := Rval { v := nsEmpty, c := build_tdefs st.next_type_stamp tds })
        (fun clk => rfl) (io_events_mono_refl _) (Nat.le_add_right _ _) (Nat.le_refl _)
        (Nat.le_refl _)
    · simp only [if_neg hc]
      exact Aux.icm_ret _ _
  · intro st env l tvs tn t
    simp only [evaluate_decs]
    exact Aux.icm_ret _ _
  · intro st env l cn ts
    simp only [evaluate_decs]
    exact Aux.icm_noclock (s' := { st with next_exn_stamp := st.next_exn_stamp + 1 })
      (r := Rval { v := nsEmpty, c := nsSing cn (ts.length, ExnStamp st.next_exn_stamp) })
      (fun clk => rfl) (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_add_right _ _)
      (Nat.le_refl _)
  · intro st env mn ds ih
    refine Aux.icm_ext (fun s => Aux.evaluate_Dmod' s env mn ds) ?_
    exact Aux.icm_bind (fun s => evaluate_decs s env ds)
      (fun r st' => (st', match r with
        | Rval env' => Rval ({ v := nsLift mn env'.v, c := nsLift mn env'.c } : sem_env value)
        | Rerr err => Rerr err)) st
      ⟨ih, fun _ _ _ => Aux.icm_ret _ _, fun _ => rfl⟩
  · intro st env lds ds ih1 ih2
    refine Aux.icm_ext (fun s => Aux.evaluate_Dlocal' s env lds ds) ?_
    exact Aux.icm_bind_val (f := fun s => evaluate_decs s env lds)
      (k := fun env1 st1 => evaluate_decs st1 (extend_dec_env env1 env) ds) ih1
      (fun s' v hs => ih2 s' _ (Aux.icm_clock ih1 hs))
  · intro st env n
    simp only [evaluate_decs]
    cases hd : declare_env st.eval_state env with
    | none =>
      refine Aux.icm_noclock (s' := st) (r := Rerr (Rabort Rtype_error))
        (fun clk => ?_) (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      simp only [hd]
    | some x =>
      obtain ⟨x, es'⟩ := x
      refine Aux.icm_noclock (s' := { st with eval_state := es' })
        (r := Rval { v := nsSing n x, c := nsEmpty })
        (fun clk => ?_) (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      simp only [hd]

/- HOL4:
Theorem is_clock_io_mono_evaluate_decs:
  !s e p. is_clock_io_mono (\s. evaluate_decs s e p) s -/
theorem is_clock_io_mono_evaluate_decs :
    ∀ (s : state ffi) (e : sem_env value) (p : List dec),
      is_clock_io_mono (fun s => evaluate_decs s e p) s := is_clock_io_mono_evaluate.2.2

/- HOL4:
Theorem is_clock_io_mono_extra:
   (!s. is_clock_io_mono f s)
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> f (s with clock := s.clock + extra)
        = (s' with clock := s'.clock + extra,r) -/
theorem is_clock_io_mono_extra {α β : Type} (f : state ffi → state ffi × result α β)
    (s s' : state ffi) (r : result α β) (extra : Nat) :
    (∀ s, is_clock_io_mono f s) →
    f s = (s', r) ∧ ¬ (r = Rerr (Rabort Rtimeout_error)) →
    f { s with clock := s.clock + extra } = ({ s' with clock := s'.clock + extra }, r) := by
  rintro h ⟨hf, hr⟩
  obtain ⟨-, a2, -, -, -, a6⟩ := (Aux.icm_iff f s).mp (h s)
  rw [hf] at a2 a6
  have a2 : s'.clock ≤ s.clock := a2
  obtain ⟨b1, b2, -, -⟩ := a6 (s.clock + extra)
  obtain ⟨c1, c2⟩ := b1 ((b2 hr).mp (by show s.clock + extra ≥ s.clock - s'.clock; omega)) hr
  refine Prod.ext ?_ c1
  rw [c2]
  show state.mk _ _ _ _ _ _ = state.mk _ _ _ _ _ _
  congr 1
  show s.clock + extra - (s.clock - s'.clock) = s'.clock + extra
  omega

/- HOL4:
Theorem list_result_eq_Rval[simp]:
  list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v -/
theorem list_result_eq_Rval {α β : Type} (r : result α β) (r' : List α) :
    list_result r = Rval r' ↔ ∃ v, r' = [v] ∧ r = Rval v := by
  cases r with
  | Rval v =>
    simp only [list_result, result.Rval.injEq]
    constructor
    · rintro rfl; exact ⟨v, rfl, rfl⟩
    · rintro ⟨w, rfl, rfl⟩; rfl
  | Rerr e => simp [list_result]

/- HOL4:
Theorem evaluate_length:
   (∀(s:'ffi state) e p s' r. evaluate s e p = (s',Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e v p er s' r. evaluate_match s e v p er = (s',Rval r) ⇒ LENGTH r = 1) ∧
   (∀(s:'ffi state) e ds s' r. evaluate_decs s e ds = (s',Rval r) ⇒ T) -/
theorem evaluate_length :
    (∀ (s : state ffi) (e : sem_env value) (p : List exp) (s' : state ffi) (r : List value),
      evaluate s e p = (s', Rval r) → r.length = p.length) ∧
    (∀ (s : state ffi) (e : sem_env value) (v : value) (p : List (pat × exp)) (er : value)
      (s' : state ffi) (r : List value),
      evaluate_match s e v p er = (s', Rval r) → r.length = 1) ∧
    (∀ (s : state ffi) (e : sem_env value) (ds : List dec) (s' : state ffi)
      (r : sem_env value),
      evaluate_decs s e ds = (s', Rval r) → True) := by
  have H := Aux.eval_induct (ffi := ffi)
    (P := fun st env es => ∀ s' r, evaluate st env es = (s', Rval r) → r.length = es.length)
    (Q := fun st env v pes err =>
      ∀ s' r, evaluate_match st env v pes err = (s', Rval r) → r.length = 1)
    (D := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨fun s e p s' r h => H.1 s e p s' r h, fun s e v p er s' r h => H.2.1 s e v p er s' r h,
      fun _ _ _ _ _ _ => trivial⟩
  · intro st env s' r h
    rw [evaluate] at h; cases h; rfl
  · intro st env e1 e2 es ih1 ih2 s' r h
    rw [evaluate] at h
    split at h
    · rename_i hf
      split at h
      · rename_i he
        cases h
        rw [List.length_cons, ih2 _ (fix_clock_le_aux hf) _ _ he]
        rfl
      · cases h
    · cases h
  · intro st env l s' r h
    rw [evaluate] at h; cases h; rfl
  · intro st env e ih s' r h
    rw [evaluate] at h
    split at h <;> cases h
  · intro st env e pes ih1 ih2 s' r h
    rw [Aux.evaluate_Handle] at h
    split at h
    · rename_i he; cases h; exact ih1 _ _ he
    · rename_i he
      split at h
      · exact ih2 _ _ (evaluate_clock.1 _ _ _ _ _ he) _ _ h
      · cases h
    · cases h
  · intro st env cn es ih s' r h
    rw [evaluate] at h
    split at h
    · split at h
      · split at h <;> cases h
        rfl
      · cases h
    · cases h
  · intro st env n s' r h
    rw [evaluate] at h
    split at h <;> cases h
    rfl
  · intro st env x e s' r h
    rw [evaluate] at h; cases h; rfl
  · intro st env o es ih1 ih2 ih3 s' r h
    rw [Aux.evaluate_App] at h
    split at h
    · rename_i st' vs he
      have hc := evaluate_clock.1 _ _ _ _ _ he
      split at h
      · split at h
        · split at h
          · cases h
          · have := ih2 (dec_clock st') _ _ (by simp only [dec_clock]; omega) _ _ h
            exact this
        · cases h
      · split at h
        · cases h
        · cases h
        · cases h; rfl
        · split at h
          · split at h
            · cases h
            · split at h
              · rename_i he2
                have := ih2 (dec_clock st') _ _ (by simp only [dec_clock]; omega) _ _ he2
                split at h <;> cases h
                exact this
              · cases h
          · cases h
      · split at h
        · split at h
          · cases h
          · split at h
            · split at h <;> cases h
              rfl
            · cases h
            · cases h
        · cases h
      · split at h
        · cases h
        · rename_i rr _
          cases rr with
          | Rval v => cases h; rfl
          | Rerr e => cases h
    · cases h
  · intro st env l e1 e2 ih1 ih2 s' r h
    rw [Aux.evaluate_Log] at h
    split at h
    · rename_i he
      split at h
      · cases h
      · rename_i hl
        rw [do_log_exp_aux hl] at h
        exact ih2 _ (evaluate_clock.1 _ _ _ _ _ he) _ _ h
      · cases h; rfl
    · cases h
  · intro st env e1 e2 e3 ih1 ih2 ih3 s' r h
    rw [Aux.evaluate_If] at h
    split at h
    · rename_i he
      have hc := evaluate_clock.1 _ _ _ _ _ he
      split at h
      · cases h
      · rename_i hl
        unfold do_if at hl
        split at hl
        · cases hl; exact ih2 _ hc _ _ h
        · split at hl
          · cases hl; exact ih3 _ hc _ _ h
          · cases hl
    · cases h
  · intro st env e pes ih1 ih2 s' r h
    rw [Aux.evaluate_Mat] at h
    split at h
    · rename_i he
      split at h
      · exact ih2 _ _ (evaluate_clock.1 _ _ _ _ _ he) _ _ h
      · cases h
    · cases h
  · intro st env xo e1 e2 ih1 ih2 s' r h
    rw [Aux.evaluate_Let] at h
    split at h
    · rename_i he
      exact ih2 _ _ (evaluate_clock.1 _ _ _ _ _ he) _ _ h
    · cases h
  · intro st env funs e ih s' r h
    rw [evaluate] at h
    split at h
    · exact ih _ _ _ h
    · cases h
  · intro st env e t ih s' r h
    rw [evaluate] at h; exact ih _ _ h
  · intro st env e l ih s' r h
    rw [evaluate] at h; exact ih _ _ h
  · intro st env v err s' r h
    rw [evaluate_match] at h; cases h
  · intro st env v p e pes err ih1 ih2 s' r h
    rw [evaluate_match] at h
    split at h
    · split at h
      · exact ih1 _ _ h
      · cases h
      · exact ih2 _ _ _ h
    · cases h
  all_goals (intros; trivial)

/- HOL4:
Theorem is_clock_io_mono_set_clock:
   is_clock_io_mono f s
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> ?ck0. f (s with clock := ck0) = (s' with clock := ck1, r) -/
theorem is_clock_io_mono_set_clock {α β : Type} (f : state ffi → state ffi × result α β)
    (s s' : state ffi) (r : result α β) (ck1 : Nat) :
    is_clock_io_mono f s →
    f s = (s', r) ∧ ¬ (r = Rerr (Rabort Rtimeout_error)) →
    ∃ ck0 : Nat, f { s with clock := ck0 } = ({ s' with clock := ck1 }, r) := by
  rintro h ⟨hf, hr⟩
  obtain ⟨-, a2, -, -, -, a6⟩ := (Aux.icm_iff f s).mp h
  rw [hf] at a2 a6
  have a2 : s'.clock ≤ s.clock := a2
  refine ⟨ck1 + (s.clock - s'.clock), ?_⟩
  obtain ⟨b1, b2, -, -⟩ := a6 (ck1 + (s.clock - s'.clock))
  obtain ⟨c1, c2⟩ := b1 ((b2 hr).mp
    (by show ck1 + (s.clock - s'.clock) ≥ s.clock - s'.clock; omega)) hr
  refine Prod.ext ?_ c1
  rw [c2]
  show state.mk _ _ _ _ _ _ = state.mk _ _ _ _ _ _
  congr 1
  show ck1 + (s.clock - s'.clock) - (s.clock - s'.clock) = ck1
  omega

/- HOL4:
Theorem is_clock_io_mono_minimal:
   is_clock_io_mono f s
    ==> f s = (s', r) /\ s'.clock = 0 /\ r <> Rerr (Rabort Rtimeout_error)
        /\ s.clock > k
    ==> (?s''. f (s with clock := k) = (s'', Rerr (Rabort Rtimeout_error)) /\
               io_events_mono s''.ffi s'.ffi) -/
theorem is_clock_io_mono_minimal {α β : Type} (f : state ffi → state ffi × result α β)
    (s s' : state ffi) (r : result α β) (k : Nat) :
    is_clock_io_mono f s →
    f s = (s', r) ∧ s'.clock = 0 ∧ r ≠ Rerr (Rabort Rtimeout_error) ∧ s.clock > k →
    (∃ s'' : state ffi, f { s with clock := k } = (s'', Rerr (Rabort Rtimeout_error)) ∧
      io_events_mono s''.ffi s'.ffi) := by
  rintro h ⟨hf, h0, hr, hk⟩
  obtain ⟨-, a2, -, -, -, a6⟩ := (Aux.icm_iff f s).mp h
  rw [hf] at a2 a6
  obtain ⟨-, b2, -, b4⟩ := a6 k
  refine ⟨(f { s with clock := k }).1, Prod.ext rfl ?_, b4 (by omega)⟩
  apply Classical.byContradiction
  intro hn
  have : k ≥ s.clock - s'.clock := (b2 hr).mpr hn
  omega

/- HOL4:
Theorem can_pmatch_all_EVERY:
  can_pmatch_all envC refs ps v <=>
  EVERY (\p. pmatch envC refs p v [] <> Match_type_error) ps -/
theorem can_pmatch_all_EVERY (envC : env_ctor) (refs : List (store_v value)) (ps : List pat)
    (v : value) :
    can_pmatch_all envC refs ps v ↔
      EVERY (fun p => pmatch envC refs p v [] ≠ Match_type_error) ps := by
  induction ps with
  | nil => simp [can_pmatch_all, EVERY]
  | cons p t ih =>
    simp only [can_pmatch_all, EVERY, ← ih]
    by_cases h : pmatch envC refs p v [] = Match_type_error <;> simp [h]

end

end CmlTS
