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

theorem Aux.isPREFIX_iff {α : Type} {l1 l2 : List α} : isPREFIX l1 l2 ↔ ∃ l3, l2 = l1 ++ l3 := by
  induction l1 generalizing l2 with
  | nil => simp [isPREFIX]
  | cons a l1 ih =>
    cases l2 with
    | nil => simp [isPREFIX]
    | cons b l2 => simp [isPREFIX, ih, eq_comm (a := a)]

/-! ## Theorems -/

/- HOL4:
Theorem io_events_mono_trans:
   io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 ⇒
   io_events_mono ffi1 ffi3 -/
theorem io_events_mono_trans (ffi1 ffi2 ffi3 : ffi_state ffi) :
    io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 → io_events_mono ffi1 ffi3 := by
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  obtain ⟨a, ha⟩ := Aux.isPREFIX_iff.1 h1
  obtain ⟨b, hb⟩ := Aux.isPREFIX_iff.1 h3
  refine ⟨Aux.isPREFIX_iff.2 ⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩, fun h => ?_⟩
  have hab : a ++ b = [] := by
    rw [hb, ha, List.append_assoc] at h
    exact List.append_right_eq_self.1 h
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hab
  rw [h4 (by simpa using hb), h2 (by simpa using ha)]

/- HOL4:
Theorem call_FFI_rel_io_events_mono:
   ∀s1 s2.
   RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2 -/
theorem call_FFI_rel_io_events_mono :
    ∀ s1 s2 : ffi_state ffi, RTC call_FFI_rel s1 s2 → io_events_mono s1 s2 := by
  have hrefl : ∀ s : ffi_state ffi, io_events_mono s s := fun s =>
    ⟨Aux.isPREFIX_iff.2 ⟨[], by simp⟩, fun _ => rfl⟩
  intro s1 s2 h
  induction h with
  | refl x => exact hrefl x
  | step x y z hxy _ ih =>
    refine io_events_mono_trans x y z ⟨?_, ih⟩
    obtain ⟨n, conf, bytes, t, hc⟩ := hxy
    unfold call_FFI at hc
    split at hc
    · split at hc
      · split at hc
        · cases hc
          exact ⟨Aux.isPREFIX_iff.2 ⟨_, rfl⟩, fun h => by simp at h⟩
        · cases hc
      · cases hc
    · cases hc; exact hrefl x

/- HOL4:
Theorem io_events_mono_refl[simp]:
   io_events_mono ffi ffi -/
theorem io_events_mono_refl {ffi_ty : Type} (ffi : ffi_state ffi_ty) :
    io_events_mono ffi ffi := call_FFI_rel_io_events_mono _ _ (RTC.refl _)

theorem Aux.store_assign_length {α : Type} {n : Nat} {v : store_v α} {s s' : List (store_v α)}
    (h : store_assign n v s = some s') : s'.length = s.length := by
  unfold store_assign at h
  split at h
  · cases h; rw [Aux.LUPDATE_eq_set]; simp
  · cases h

theorem Aux.store_alloc_length {α : Type} {n : Nat} {v : store_v α} {s s' : List (store_v α)}
    (h : store_alloc v s = (s', n)) : s.length ≤ s'.length := by
  unfold store_alloc at h
  cases h; simp

section do_app_inv

variable {ffi_ty : Type} {r r' w : List (store_v value)} {ffi ffi' t' : ffi_state ffi_ty}

def Aux.do_app_post (r r' : List (store_v value)) (ffi ffi' : ffi_state ffi_ty) : Prop :=
  r.length ≤ r'.length ∧ (ffi' = ffi ∨ call_FFI_rel ffi ffi')

theorem Aux.do_app_L1 (h : (r, ffi) = (r', ffi')) : Aux.do_app_post r r' ffi ffi' := by
  cases h; exact ⟨Nat.le_refl _, Or.inl rfl⟩

theorem Aux.do_app_L2 {n : Nat} {v : store_v value} (h1 : store_assign n v r = some w)
    (h : (w, ffi) = (r', ffi')) : Aux.do_app_post r r' ffi ffi' := by
  cases h; exact ⟨Nat.le_of_eq (Aux.store_assign_length h1).symm, Or.inl rfl⟩

theorem Aux.do_app_L3 {n : Nat} {v : store_v value} (h1 : store_alloc v r = (w, n))
    (h : (w, ffi) = (r', ffi')) : Aux.do_app_post r r' ffi ffi' := by
  cases h; exact ⟨Aux.store_alloc_length h1, Or.inl rfl⟩

theorem Aux.do_app_L4 {n : Nat} {v : store_v value} {nm : ffiname} {conf bytes t : List word8}
    (h2 : call_FFI ffi nm conf bytes = FFI_return t' t)
    (h1 : store_assign n v r = some w)
    (h : (w, t') = (r', ffi')) : Aux.do_app_post r r' ffi ffi' := by
  cases h
  exact ⟨Nat.le_of_eq (Aux.store_assign_length h1).symm, Or.inr ⟨_, _, _, _, h2⟩⟩

theorem Aux.do_app_L5 {β : Type} {o : thunk_op_t} {vs : List value} {res : result value β}
    (h : thunk_op (r, ffi) o vs = some ((r', ffi'), res)) : Aux.do_app_post r r' ffi ffi' := by
  unfold thunk_op at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨Aux.store_alloc_length rfl, Or.inl rfl⟩
  · split at h
    · cases h
      rename_i h1
      exact ⟨Nat.le_of_eq (Aux.store_assign_length h1).symm, Or.inl rfl⟩
    · cases h
  · cases h

theorem Aux.do_app_inv {op : CmlTS.op} {vs : List value} {res : result value value}
    (h : do_app (r, ffi) op vs = some ((r', ffi'), res)) : Aux.do_app_post r r' ffi ffi' := by
  rw [do_app_cases] at h
  repeat' first
    | (cases h with
       | inl h => ?_
       | inr h => ?_)
    | (obtain ⟨_, h⟩ := h)
  all_goals first
    | (apply Aux.do_app_L1; assumption; done)
    | (apply Aux.do_app_L2; assumption; assumption; done)
    | (apply Aux.do_app_L3; assumption; assumption; done)
    | (apply Aux.do_app_L4; assumption; assumption; assumption; done)
    | (apply Aux.do_app_L5; assumption; done)

end do_app_inv

/- HOL4:
Theorem do_app_call_FFI_rel:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi' -/
theorem do_app_call_FFI_rel {ffi_ty : Type} (r r' : List (store_v value))
    (ffi ffi' : ffi_state ffi_ty) (op : CmlTS.op) (vs : List value) (res : result value value) :
    do_app (r, ffi) op vs = some ((r', ffi'), res) → RTC call_FFI_rel ffi ffi' := by
  intro h
  rcases (Aux.do_app_inv h).2 with rfl | h
  · exact RTC.refl _
  · exact RTC.step _ _ _ h (RTC.refl _)

/- HOL4:
Theorem do_app_io_events_mono:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi' -/
theorem do_app_io_events_mono {ffi_ty : Type} (r r' : List (store_v value))
    (ffi ffi' : ffi_state ffi_ty) (op : CmlTS.op) (vs : List value) (res : result value value) :
    do_app (r, ffi) op vs = some ((r', ffi'), res) → io_events_mono ffi ffi' := fun h =>
  call_FFI_rel_io_events_mono _ _ (do_app_call_FFI_rel _ _ _ _ _ _ _ h)

section icm

variable {α β γ δ : Type}

/-- The content of `is_clock_io_mono` with the two runs named. -/
def Aux.icm_rel (s s' : state ffi) (r : result α β) (clk : Nat) (s'' : state ffi)
    (r' : result α β) : Prop :=
  (¬ (r' = Rerr (Rabort Rtimeout_error)) → ¬ (r = Rerr (Rabort Rtimeout_error)) →
    r' = r ∧ s'' = { s' with clock := clk - (s.clock - s'.clock) }) ∧
  (¬ (r = Rerr (Rabort Rtimeout_error)) →
    (clk ≥ s.clock - s'.clock ↔ ¬ (r' = Rerr (Rabort Rtimeout_error)))) ∧
  (¬ (r' = Rerr (Rabort Rtimeout_error)) → clk ≤ s.clock →
    ¬ (r = Rerr (Rabort Rtimeout_error))) ∧
  (clk ≤ s.clock → io_events_mono s''.ffi s'.ffi)

theorem Aux.icm_iff {f : state ffi → state ffi × result α β} {s s' : state ffi} {r : result α β}
    (h : f s = (s', r)) :
    is_clock_io_mono f s ↔
      io_events_mono s.ffi s'.ffi ∧ s'.clock ≤ s.clock ∧
      s.next_type_stamp ≤ s'.next_type_stamp ∧ s.next_exn_stamp ≤ s'.next_exn_stamp ∧
      s.refs.length ≤ s'.refs.length ∧
      (∀ clk s'' r', f { s with clock := clk } = (s'', r') → Aux.icm_rel s s' r clk s'' r') := by
  unfold is_clock_io_mono
  rw [h]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, h5, fun clk s'' r' e => ?_⟩
    have := h6 clk
    rw [e] at this
    exact this
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, h5, fun clk => ?_⟩
    exact h6 clk _ _ rfl

theorem Aux.icm_congr {f : state ffi → state ffi × result α β} {t : state ffi}
    (g : state ffi → state ffi × result α β)
    (h : ∀ clk, f { t with clock := clk } = g { t with clock := clk })
    (hg : is_clock_io_mono g t) : is_clock_io_mono f t := by
  have h0 : f t = g t := h t.clock
  rcases hgt : g t with ⟨s', r⟩
  rw [hgt] at h0
  rw [Aux.icm_iff hgt] at hg
  rw [Aux.icm_iff h0]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
  exact ⟨h1, h2, h3, h4, h5, fun clk s'' r' e => h6 clk s'' r' ((h clk).symm.trans e)⟩

/-- Functions that do not look at the clock. -/
theorem Aux.icm_simple {f : state ffi → state ffi × result α β} {t t' : state ffi}
    {r : result α β} (h : ∀ clk, f { t with clock := clk } = ({ t' with clock := clk }, r))
    (hio : io_events_mono t.ffi t'.ffi) (hts : t.next_type_stamp ≤ t'.next_type_stamp)
    (hes : t.next_exn_stamp ≤ t'.next_exn_stamp) (hr : t.refs.length ≤ t'.refs.length) :
    is_clock_io_mono f t := by
  have h0 : f t = ({ t' with clock := t.clock }, r) := h t.clock
  rw [Aux.icm_iff h0]
  refine ⟨hio, Nat.le_refl _, hts, hes, hr, fun clk s'' r' e => ?_⟩
  rw [h] at e
  cases e
  refine ⟨fun _ _ => ⟨rfl, ?_⟩, fun h => ?_, fun h _ => h, fun _ => io_refl _⟩
  · simp
  · simp [h]
where
  io_refl (x : ffi_state ffi) : io_events_mono x x := io_events_mono_refl x

theorem Aux.icm_const (s : state ffi) (r : result α β) :
    is_clock_io_mono (fun s : state ffi => (s, r)) s :=
  Aux.icm_simple (t' := s) (fun _ => rfl) (io_events_mono_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _)

/-- Precomposition with a change of the evaluation state. -/
theorem Aux.icm_pre {k : state ffi → state ffi × result α β} {s : state ffi}
    {es : Option eval_state} (h : is_clock_io_mono k { s with eval_state := es }) :
    is_clock_io_mono (fun s => k { s with eval_state := es }) s := by
  rcases hk : k { s with eval_state := es } with ⟨s', r⟩
  rw [Aux.icm_iff hk] at h
  rw [Aux.icm_iff (f := fun s => k { s with eval_state := es }) hk]
  exact h

end icm

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
  exact ⟨fun hf => Aux.icm_congr f
      (fun clk => (h { s with clock := clk } ⟨rfl, rfl, rfl⟩).symm) hf,
    fun hg => Aux.icm_congr g (fun clk => h { s with clock := clk } ⟨rfl, rfl, rfl⟩) hg⟩

/- HOL4:
Theorem is_clock_io_mono_return:
   is_clock_io_mono (\s. (s,Rval r)) s -/
theorem is_clock_io_mono_return {α β : Type} (r : α) (s : state ffi) :
    is_clock_io_mono (fun s : state ffi => (s, (Rval r : result α β))) s := Aux.icm_const _ _

/- HOL4:
Theorem is_clock_io_mono_err:
   is_clock_io_mono (\s. (s,Rerr r)) s -/
theorem is_clock_io_mono_err {α β : Type} (r : error_result β) (s : state ffi) :
    is_clock_io_mono (fun s : state ffi => (s, (Rerr r : result α β))) s := Aux.icm_const _ _

/- HOL4:
Theorem pair_CASE_eq_forall:
   (case x of (a, b) => P a b) = (!a b. x = (a, b) ==> P a b) -/
theorem pair_CASE_eq_forall {α β : Type} (x : α × β) (P : α → β → Prop) :
    (match x with | (a, b) => P a b) ↔ (∀ a b, x = (a, b) → P a b) := by
  obtain ⟨a, b⟩ := x
  constructor
  · rintro h a' b' e; cases e; exact h
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
  rintro ⟨hf, hg, hT⟩
  rcases hfs : f s with ⟨s1, r1⟩
  rcases hgs : g r1 s1 with ⟨s2, r2⟩
  have hg1 := hg _ _ hfs
  rw [Aux.icm_iff hfs] at hf
  rw [Aux.icm_iff hgs] at hg1
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hg1
  have hh : (fun s => match f s with | (s', r) => g r s') s = (s2, r2) := by
    show (match f s with | (s', r) => g r s') = _
    rw [hfs]; exact hgs
  refine (Aux.icm_iff (f := fun s => match f s with | (s', r) => g r s') hh).2 ?_
  refine ⟨io_events_mono_trans _ _ _ ⟨f1, g1⟩, by omega, by omega, by omega, by omega, ?_⟩
  intro clk s2' r2' e
  have e : (match f { s with clock := clk } with | (s', r) => g r s') = (s2', r2') := e
  rcases hfc : f { s with clock := clk } with ⟨s1', r1'⟩
  rw [hfc] at e
  have e : g r1' s1' = (s2', r2') := e
  obtain ⟨F1, F2, F3, F4⟩ := f6 clk s1' r1' hfc
  by_cases h1 : r1 = Rerr (Rabort Rtimeout_error)
  · subst h1
    rw [hT] at hgs
    cases hgs
    by_cases h1' : r1' = Rerr (Rabort Rtimeout_error)
    · subst h1'
      rw [hT] at e
      cases e
      exact ⟨fun h => absurd rfl h, fun h => absurd rfl h, fun h => absurd rfl h, F4⟩
    · have hn : ¬ clk ≤ s.clock := fun h => F3 h1' h rfl
      exact ⟨fun _ h => absurd rfl h, fun h => absurd rfl h, fun _ h => absurd h hn,
        fun h => absurd h hn⟩
  · by_cases h1' : r1' = Rerr (Rabort Rtimeout_error)
    · subst h1'
      rw [hT] at e
      cases e
      have hn : ¬ clk ≥ s.clock - s1.clock := fun h => (F2 h1).1 h rfl
      refine ⟨fun h => absurd rfl h, fun _ => ⟨fun h => ?_, fun h => absurd rfl h⟩,
        fun h => absurd rfl h, fun h => io_events_mono_trans _ _ _ ⟨F4 h, g1⟩⟩
      exact absurd h (by omega)
    · obtain ⟨rfl, rfl⟩ := F1 h1' h1
      have hge := (F2 h1).2 h1'
      obtain ⟨G1, G2, G3, G4⟩ := g6 _ _ _ e
      refine ⟨fun h h' => ?_, fun h => ?_, fun h h' => G3 h (by omega), fun h => G4 (by omega)⟩
      · obtain ⟨rfl, rfl⟩ := G1 h h'
        refine ⟨rfl, ?_⟩
        congr 1
        omega
      · rw [← G2 h]
        omega

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
  by_cases h0 : s.clock = 0
  · have hs : (fun s : state ffi => if s.clock = 0 then
        (s, (Rerr (Rabort Rtimeout_error) : result α β)) else f s) s =
        (s, Rerr (Rabort Rtimeout_error)) := if_pos h0
    refine (Aux.icm_iff (f := fun s : state ffi => if s.clock = 0 then
        (s, (Rerr (Rabort Rtimeout_error) : result α β)) else f s) hs).2 ?_
    refine ⟨io_events_mono_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro clk s'' r' e
    have e : (if clk = 0 then
        ({ s with clock := clk }, (Rerr (Rabort Rtimeout_error) : result α β))
        else f { s with clock := clk }) = (s'', r') := e
    by_cases hc : clk = 0
    · rw [if_pos hc] at e
      cases e
      exact ⟨fun h => absurd rfl h, fun h => absurd rfl h, fun h => absurd rfl h,
        fun _ => io_events_mono_refl _⟩
    · exact ⟨fun _ h => absurd rfl h, fun h => absurd rfl h, fun _ h => absurd h (by omega),
        fun h => absurd h (by omega)⟩
  · have h := h h0
    have hadj : ∀ c, 0 < c → (adj_clock 1 0 { s with clock := c - 1 }) = { s with clock := c } := by
      intro c hc
      simp only [adj_clock]
      congr 1
      omega
    rcases hfs : f s with ⟨s', r⟩
    have hd : (fun s => f (adj_clock 1 0 s)) (dec_clock s) = (s', r) := by
      show f (adj_clock 1 0 { s with clock := s.clock - 1 }) = _
      rw [hadj _ (by omega)]; exact hfs
    have hs : (fun s : state ffi => if s.clock = 0 then
        (s, (Rerr (Rabort Rtimeout_error) : result α β)) else f s) s = (s', r) :=
      (if_neg h0).trans hfs
    replace h := (Aux.icm_iff (f := fun s => f (adj_clock 1 0 s)) hd).1 h
    refine (Aux.icm_iff (f := fun s : state ffi => if s.clock = 0 then
        (s, (Rerr (Rabort Rtimeout_error) : result α β)) else f s) hs).2 ?_
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have h2 : s'.clock ≤ s.clock - 1 := h2
    refine ⟨h1, by omega, h3, h4, h5, ?_⟩
    intro clk s'' r' e
    have e : (if clk = 0 then
        ({ s with clock := clk }, (Rerr (Rabort Rtimeout_error) : result α β))
        else f { s with clock := clk }) = (s'', r') := e
    by_cases hc : clk = 0
    · rw [if_pos hc] at e
      cases e
      refine ⟨fun h => absurd rfl h, fun _ => ⟨fun h => ?_, fun h => absurd rfl h⟩,
        fun h => absurd rfl h, fun _ => h1⟩
      exact absurd h (by omega)
    · rw [if_neg hc] at e
      have e' : (fun s => f (adj_clock 1 0 s)) { dec_clock s with clock := clk - 1 } =
          (s'', r') := by
        show f (adj_clock 1 0 { s with clock := clk - 1 }) = _
        rw [hadj _ (by omega)]; exact e
      obtain ⟨G1, G2, G3, G4⟩ := h6 _ _ _ e'
      have hdc : (dec_clock s).clock = s.clock - 1 := rfl
      rw [hdc] at G1 G2 G3 G4
      refine ⟨fun h h' => ?_, fun h => ?_, fun h h' => G3 h (by omega), fun h => G4 (by omega)⟩
      · obtain ⟨rfl, rfl⟩ := G1 h h'
        refine ⟨rfl, ?_⟩
        congr 1
        omega
      · rw [← G2 h]
        omega

/- HOL4:
Theorem dec_inc_clock:
  dec_clock (adj_clock 1 0 s) = s -/
theorem dec_inc_clock (s : state ffi) : dec_clock (adj_clock 1 0 s) = s := by
  simp [dec_clock, adj_clock]

/- HOL4:
Theorem do_app_refs_length:
   do_app refs_ffi op vs = SOME res ==>
   LENGTH (FST refs_ffi) <= LENGTH (FST (FST res)) -/
theorem do_app_refs_length (refs_ffi : List (store_v value) × ffi_state ffi) (op : CmlTS.op)
    (vs : List value) (res : (List (store_v value) × ffi_state ffi) × result value value) :
    do_app refs_ffi op vs = some res → refs_ffi.1.length ≤ res.1.1.length := by
  obtain ⟨r, f⟩ := refs_ffi
  obtain ⟨⟨r', f'⟩, v⟩ := res
  exact fun h => (Aux.do_app_inv h).1

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
  cases hd : do_app (st.refs, st.ffi) op xs with
  | none =>
    refine Aux.icm_simple (t' := st) (r := Rerr (Rabort Rtype_error)) (fun clk => ?_)
      (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    dsimp only
    rw [hd]
  | some p =>
    obtain ⟨⟨refs, ffi'⟩, r⟩ := p
    refine Aux.icm_simple (t' := { st with refs := refs, ffi := ffi' }) (r := list_result r)
      (fun clk => ?_) (do_app_io_events_mono _ _ _ _ _ _ _ hd) (Nat.le_refl _) (Nat.le_refl _)
      (do_app_refs_length _ _ _ _ hd)
    dsimp only
    rw [hd]

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
  have hT : ∀ {α β : Type} (f : state ffi → state ffi × result α β) {γ : Type}
      (g : result α β → state ffi → state ffi × result γ β) (s : state ffi)
      (F : state ffi → state ffi × result γ β)
      (_ : ∀ s, F s = match f s with | (s', r) => g r s')
      (_ : is_clock_io_mono f s) (_ : ∀ s' r, f s = (s', r) → is_clock_io_mono (g r) s')
      (_ : ∀ s', g (Rerr (Rabort Rtimeout_error)) s' = (s', Rerr (Rabort Rtimeout_error))),
      is_clock_io_mono F s := by
    intro α β f γ g s F hF h1 h2 h3
    rw [funext hF]
    exact is_clock_io_mono_bind f g s ⟨h1, h2, h3⟩
  apply Aux.full_evaluate_ind
  case nil => intro st env; simp only [evaluate]; exact Aux.icm_const _ _
  case cons2 =>
    intro st env e1 e2 es ih1 ih2
    refine hT (fun s => evaluate s env [e1])
      (fun r st' => match r with
        | Rval v1 =>
          match evaluate st' env (e2 :: es) with
          | (st'', Rval vs) => (st'', Rval (HD v1 :: vs))
          | (st'', Rerr v8) => (st'', Rerr v8)
        | Rerr v10 => (st', Rerr v10)) st _ ?_ ih1 ?_ (fun _ => rfl)
    · intro s
      dsimp only
      rw [Aux.evaluate_cons2]
      rcases evaluate s env [e1] with ⟨_, _ | _⟩ <;> rfl
    · rintro s' (v1 | e) h
      · refine hT (fun s => evaluate s env (e2 :: es))
          (fun r st' => match r with
            | Rval vs => (st', Rval (HD v1 :: vs))
            | Rerr v8 => (st', Rerr v8)) s' _ ?_ (ih2 _ _ h) ?_ (fun _ => rfl)
        · intro s
          dsimp only
          rcases evaluate s env (e2 :: es) with ⟨_, _ | _⟩ <;> rfl
        · rintro s'' (v2 | e) _ <;> exact Aux.icm_const _ _
      · exact Aux.icm_const _ _
  case lit => intro st env l; simp only [evaluate]; exact Aux.icm_const _ _
  case raise =>
    intro st env e ih
    refine hT (fun s => evaluate s env [e])
      (fun r st' => match r with
        | Rval v => (st', Rerr (Rraise (HD v)))
        | Rerr v8 => (st', Rerr v8)) st _ ?_ ih ?_ (fun _ => rfl)
    · intro s
      dsimp only
      rw [evaluate]
      rcases evaluate s env [e] with ⟨_, _ | _⟩ <;> rfl
    · rintro s' (v | e) _ <;> exact Aux.icm_const _ _
  case handle =>
    intro st env e pes ih1 ih2
    refine hT (fun s => evaluate s env [e])
      (fun r st' => match r with
        | Rval v7 => (st', Rval v7)
        | Rerr (Rraise v) =>
          if can_pmatch_all env.c st'.refs (pes.map Prod.fst) v then
            evaluate_match st' env v pes v
          else (st', Rerr (Rabort Rtype_error))
        | Rerr (Rabort v12) => (st', Rerr (Rabort v12))) st _ ?_ ih1 ?_ (fun _ => rfl)
    · intro s
      dsimp only
      rw [Aux.evaluate_Handle]
      rcases evaluate s env [e] with ⟨_, _ | (_ | _)⟩ <;> rfl
    · rintro s' (v | v | a) h
      · exact Aux.icm_const _ _
      · by_cases hp : can_pmatch_all env.c s'.refs (pes.map Prod.fst) v
        · exact Aux.icm_congr _ (fun clk => if_pos hp) (ih2 _ _ h hp)
        · exact Aux.icm_congr _ (fun clk => if_neg hp) (Aux.icm_const _ _)
      · exact Aux.icm_const _ _
  case con =>
    intro st env cn es ih
    by_cases hc : do_con_check env.c cn es.length
    · refine hT (fun s => evaluate s env es.reverse)
        (fun r st' => match r with
          | Rval vs =>
            match build_conv env.c cn vs.reverse with
            | none => (st', Rerr (Rabort Rtype_error))
            | some v => (st', Rval [v])
          | Rerr v8 => (st', Rerr v8)) st _ ?_ (ih hc) ?_ (fun _ => rfl)
      · intro s
        dsimp only
        rw [evaluate, if_pos hc]
        rcases evaluate s env es.reverse with ⟨_, _ | _⟩ <;> rfl
      · rintro s' (v | e) _
        · dsimp only
          cases build_conv env.c cn v.reverse <;> exact Aux.icm_const _ _
        · exact Aux.icm_const _ _
    · refine Aux.icm_congr _ (fun clk => ?_) (Aux.icm_const st (Rerr (Rabort Rtype_error)))
      rw [evaluate, if_neg hc]
  case var =>
    intro st env n
    simp only [evaluate]
    cases nsLookup env.v n <;> exact Aux.icm_const _ _
  case func => intro st env x e; simp only [evaluate]; exact Aux.icm_const _ _
  case app =>
    intro st env o es ih1 ih2 ih3 ih4
    refine hT (fun s => evaluate s env es.reverse)
      (fun r st' => match r with
        | Rval vs =>
          match getOpClass o with
          | FunApp =>
            match do_opapp vs.reverse with
            | some (env', e) =>
              if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error))
              else evaluate (dec_clock st') env' [e]
            | none => (st', Rerr (Rabort Rtype_error))
          | Force =>
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
          | EvalOp =>
            match do_eval_res (β := value) vs.reverse st' with
            | (st1, Rval (env1, decs)) =>
              if st1.clock = 0 then (st1, Rerr (Rabort Rtimeout_error))
              else
                match evaluate_decs (dec_clock st1) env1 decs with
                | (st2, Rval env2) =>
                  match declare_env st2.eval_state (extend_dec_env env2 env1) with
                  | some (x, es2) =>
                    ({ st2 with eval_state := reset_env_generation st'.eval_state es2 }, Rval [x])
                  | none => (st2, Rerr (Rabort Rtype_error))
                | (st2, Rerr (Rabort a)) => (st2, Rerr (Rabort a))
                | (st2, Rerr e) =>
                  ({ st2 with
                      eval_state := reset_env_generation st'.eval_state st2.eval_state }, Rerr e)
            | (st1, Rerr e) => (st1, Rerr e)
          | Simple =>
            match do_app (st'.refs, st'.ffi) o vs.reverse with
            | none => (st', Rerr (Rabort Rtype_error))
            | some ((refs, ffi), r) => ({ st' with refs := refs, ffi := ffi }, list_result r)
        | Rerr e => (st', Rerr e)) st _ ?_ ih1 ?_ (fun _ => rfl)
    · intro s
      dsimp only
      rw [Aux.evaluate_App]
      rcases evaluate s env es.reverse with ⟨_, _ | _⟩ <;> rfl
    · rintro s' (vs | e) h
      · dsimp only
        cases ho : getOpClass o with
        | FunApp =>
          dsimp only
          cases hop : do_opapp vs.reverse with
          | none => exact Aux.icm_const _ _
          | some p =>
            obtain ⟨env', e⟩ := p
            refine is_clock_io_mono_check (fun s => evaluate (dec_clock s) env' [e]) s' fun hc => ?_
            simp only [dec_inc_clock]
            exact ih2 _ _ _ _ h ho hop hc
        | Force =>
          dsimp only
          cases hd : dest_thunk vs.reverse s'.refs with
          | BadRef =>
            refine Aux.icm_congr _ (fun clk => ?_) (Aux.icm_const s' (Rerr (Rabort Rtype_error)))
            dsimp only; rw [hd]
          | NotThunk =>
            refine Aux.icm_congr _ (fun clk => ?_) (Aux.icm_const s' (Rerr (Rabort Rtype_error)))
            dsimp only; rw [hd]
          | IsThunk m f =>
            cases m with
            | Evaluated =>
              refine Aux.icm_congr _ (fun clk => ?_) (Aux.icm_const s' (Rval [f]))
              dsimp only; rw [hd]
            | NotEvaluated =>
              cases hop : do_opapp [f, Conv none []] with
              | none =>
                refine Aux.icm_congr _ (fun clk => ?_)
                  (Aux.icm_const s' (Rerr (Rabort Rtype_error)))
                dsimp only; rw [hd]; dsimp only; rw [hop]
              | some p =>
                obtain ⟨env', e⟩ := p
                refine Aux.icm_congr (fun st' => if st'.clock = 0 then
                    (st', Rerr (Rabort Rtimeout_error))
                    else (fun st' => match evaluate (dec_clock st') env' [e] with
                      | (st2, Rval vs2) =>
                        match update_thunk vs.reverse st2.refs vs2 with
                        | none => (st2, Rerr (Rabort Rtype_error))
                        | some refs => ({ st2 with refs := refs }, Rval vs2)
                      | (st2, Rerr e) => (st2, Rerr e)) st') (fun clk => ?_) ?_
                · dsimp only; rw [hd]; dsimp only; rw [hop]
                · refine is_clock_io_mono_check _ s' fun hc => ?_
                  simp only [dec_inc_clock]
                  refine hT (fun s => evaluate s env' [e])
                    (fun r st2 => match r with
                      | Rval vs2 =>
                        match update_thunk vs.reverse st2.refs vs2 with
                        | none => (st2, Rerr (Rabort Rtype_error))
                        | some refs => ({ st2 with refs := refs }, Rval vs2)
                      | Rerr e => (st2, Rerr e)) _ _ ?_ (ih3 _ _ _ _ _ h ho hd hop hc) ?_
                    (fun _ => rfl)
                  · intro s
                    dsimp only
                    rcases evaluate s env' [e] with ⟨_, _ | _⟩ <;> rfl
                  · rintro s2 (vs2 | e2) _
                    · cases hu : update_thunk vs.reverse s2.refs vs2 with
                      | none =>
                        refine Aux.icm_congr _ (fun clk => ?_)
                          (Aux.icm_const s2 (Rerr (Rabort Rtype_error)))
                        dsimp only; rw [hu]
                      | some refs =>
                        refine Aux.icm_simple (t' := { s2 with refs := refs }) (r := Rval vs2)
                          (fun clk => ?_) (io_events_mono_refl _) (Nat.le_refl _)
                          (Nat.le_refl _) ?_
                        · dsimp only; rw [hu]
                        · unfold update_thunk at hu
                          split at hu
                          · split at hu
                            · exact Nat.le_of_eq (Aux.store_assign_length hu).symm
                            · cases hu
                          · cases hu
                    · exact Aux.icm_const _ _
        | EvalOp =>
          dsimp only
          cases he : do_eval vs.reverse s'.eval_state with
          | none =>
            refine Aux.icm_congr _ (fun clk => ?_) (Aux.icm_const s' (Rerr (Rabort Rtype_error)))
            dsimp only [do_eval_res]; rw [he]
          | some p =>
            obtain ⟨env1, decs, es1⟩ := p
            refine Aux.icm_congr _ ?_ (Aux.icm_pre (es := es1) (k := fun st1 => if st1.clock = 0 then
                (st1, Rerr (Rabort Rtimeout_error))
              else
                (fun st1 => match evaluate_decs (dec_clock st1) env1 decs with
                | (st2, Rval env2) =>
                  match declare_env st2.eval_state (extend_dec_env env2 env1) with
                  | some (x, es2) =>
                    ({ st2 with eval_state := reset_env_generation s'.eval_state es2 }, Rval [x])
                  | none => (st2, Rerr (Rabort Rtype_error))
                | (st2, Rerr (Rabort a)) => (st2, Rerr (Rabort a))
                | (st2, Rerr e) =>
                  ({ st2 with
                      eval_state := reset_env_generation s'.eval_state st2.eval_state },
                        Rerr e)) st1) ?_)
            · intro clk
              dsimp only [do_eval_res]; rw [he]
            · refine is_clock_io_mono_check _ _ fun hc => ?_
              simp only [dec_inc_clock]
              have hR := ih4 s' vs { s' with eval_state := es1 } env1 decs h ho (by
                simp only [do_eval_res, he]) hc
              refine hT (fun s => evaluate_decs s env1 decs)
                (fun r st2 => match r with
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
                          Rerr e)) _ _ ?_ hR ?_ (fun _ => rfl)
              · intro s
                dsimp only
                rcases evaluate_decs s env1 decs with ⟨_, _ | (_ | _)⟩ <;> rfl
              · rintro s2 (env2 | v2 | a) _
                · cases hde : declare_env s2.eval_state (extend_dec_env env2 env1) with
                  | none =>
                    refine Aux.icm_congr _ (fun clk => ?_)
                      (Aux.icm_const s2 (Rerr (Rabort Rtype_error)))
                    dsimp only; rw [hde]
                  | some p =>
                    obtain ⟨x, es2⟩ := p
                    refine Aux.icm_simple (t' := { s2 with
                        eval_state := reset_env_generation s'.eval_state es2 }) (r := Rval [x])
                      (fun clk => ?_) (io_events_mono_refl _) (Nat.le_refl _)
                      (Nat.le_refl _) (Nat.le_refl _)
                    dsimp only; rw [hde]
                · exact Aux.icm_simple (t' := { s2 with
                        eval_state := reset_env_generation s'.eval_state s2.eval_state })
                      (r := Rerr (Rraise v2))
                      (fun clk => rfl) (io_events_mono_refl _) (Nat.le_refl _)
                      (Nat.le_refl _) (Nat.le_refl _)
                · exact Aux.icm_const _ _
        | Simple => exact is_clock_io_mono_do_app_simple o _ _
      · exact Aux.icm_const _ _
  case log =>
    intro st env l e1 e2 ih1 ih2
    refine hT (fun s => evaluate s env [e1])
      (fun r st' => match r with
        | Rval v1 =>
          match do_log l (HD v1) e2 with
          | none => (st', Rerr (Rabort Rtype_error))
          | some (Exp e) => evaluate st' env [e]
          | some (Val v) => (st', Rval [v])
        | Rerr v9 => (st', Rerr v9)) st _ ?_ ih1 ?_ (fun _ => rfl)
    · intro s
      dsimp only
      rw [Aux.evaluate_Log]
      rcases evaluate s env [e1] with ⟨_, _ | _⟩ <;> rfl
    · rintro s' (v | e) h
      · dsimp only
        rcases hl : do_log l (HD v) e2 with _ | (e | v')
        · exact Aux.icm_const _ _
        · exact ih2 _ _ _ h hl
        · exact Aux.icm_const _ _
      · exact Aux.icm_const _ _
  case ite =>
    intro st env e1 e2 e3 ih1 ih2
    refine hT (fun s => evaluate s env [e1])
      (fun r st' => match r with
        | Rval v =>
          match do_if (HD v) e2 e3 with
          | none => (st', Rerr (Rabort Rtype_error))
          | some e => evaluate st' env [e]
        | Rerr v8 => (st', Rerr v8)) st _ ?_ ih1 ?_ (fun _ => rfl)
    · intro s
      dsimp only
      rw [Aux.evaluate_If]
      rcases evaluate s env [e1] with ⟨_, _ | _⟩ <;> rfl
    · rintro s' (v | e) h
      · dsimp only
        rcases hl : do_if (HD v) e2 e3 with _ | e
        · exact Aux.icm_const _ _
        · exact ih2 _ _ _ h hl
      · exact Aux.icm_const _ _
  case mat =>
    intro st env e pes ih1 ih2
    refine hT (fun s => evaluate s env [e])
      (fun r st' => match r with
        | Rval v =>
          if can_pmatch_all env.c st'.refs (pes.map Prod.fst) (HD v) then
            evaluate_match st' env (HD v) pes bind_exn_v
          else (st', Rerr (Rabort Rtype_error))
        | Rerr v8 => (st', Rerr v8)) st _ ?_ ih1 ?_ (fun _ => rfl)
    · intro s
      dsimp only
      rw [Aux.evaluate_Mat]
      rcases evaluate s env [e] with ⟨_, _ | _⟩ <;> rfl
    · rintro s' (v | e) h
      · by_cases hp : can_pmatch_all env.c s'.refs (pes.map Prod.fst) (HD v)
        · exact Aux.icm_congr _ (fun clk => if_pos hp) (ih2 _ _ h hp)
        · exact Aux.icm_congr _ (fun clk => if_neg hp) (Aux.icm_const _ _)
      · exact Aux.icm_const _ _
  case letc =>
    intro st env xo e1 e2 ih1 ih2
    refine hT (fun s => evaluate s env [e1])
      (fun r st' => match r with
        | Rval v => evaluate st' { env with v := nsOptBind xo (HD v) env.v } [e2]
        | Rerr v8 => (st', Rerr v8)) st _ ?_ ih1 ?_ (fun _ => rfl)
    · intro s
      dsimp only
      rw [Aux.evaluate_Let]
      rcases evaluate s env [e1] with ⟨_, _ | _⟩ <;> rfl
    · rintro s' (v | e) h
      · exact ih2 _ _ h
      · exact Aux.icm_const _ _
  case letrec =>
    intro st env funs e ih
    by_cases hd : ALL_DISTINCT (funs.map (fun (x, _, _) => x))
    · refine Aux.icm_congr _ (fun clk => ?_) (ih hd)
      rw [evaluate, if_pos hd]
    · refine Aux.icm_congr _ (fun clk => ?_) (Aux.icm_const st (Rerr (Rabort Rtype_error)))
      rw [evaluate, if_neg hd]
  case tannot => intro st env e t ih; simp only [evaluate]; exact ih
  case lannot => intro st env e l ih; simp only [evaluate]; exact ih
  case mnil => intro st env v v'; simp only [evaluate_match]; exact Aux.icm_const _ _
  case mcons =>
    intro st env v p e pes v' ih1 ih2
    by_cases hd : ALL_DISTINCT (pat_bindings p [])
    · cases hp : pmatch env.c st.refs p v [] with
      | No_match =>
        refine Aux.icm_congr _ (fun clk => ?_) (ih1 hd hp)
        rw [evaluate_match, if_pos hd, hp]
      | Match_type_error =>
        refine Aux.icm_congr _ (fun clk => ?_) (Aux.icm_const st (Rerr (Rabort Rtype_error)))
        rw [evaluate_match, if_pos hd, hp]
      | Match env_v' =>
        refine Aux.icm_congr _ (fun clk => ?_) (ih2 _ hd hp)
        rw [evaluate_match, if_pos hd, hp]
    · refine Aux.icm_congr _ (fun clk => ?_) (Aux.icm_const st (Rerr (Rabort Rtype_error)))
      rw [evaluate_match, if_neg hd]
  case dnil => intro st env; simp only [evaluate_decs]; exact Aux.icm_const _ _
  case dcons2 =>
    intro st env d1 d2 ds ih1 ih2
    refine hT (fun s => evaluate_decs s env [d1])
      (fun r st1 => match r with
        | Rval env1 =>
          match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds) with
          | (st2, r) => (st2, combine_dec_result env1 r)
        | Rerr v7 => (st1, Rerr v7)) st _ ?_ ih1 ?_ (fun _ => rfl)
    · intro s
      dsimp only
      rw [Aux.evaluate_decs_cons2]
      rcases evaluate_decs s env [d1] with ⟨_, _ | _⟩ <;> rfl
    · rintro s' (env1 | e) h
      · refine hT (fun s => evaluate_decs s (extend_dec_env env1 env) (d2 :: ds))
          (fun r st2 => (st2, combine_dec_result env1 r)) s' _ (fun _ => rfl) (ih2 _ _ h) ?_
          (fun _ => rfl)
        rintro s'' r _
        exact Aux.icm_const _ _
      · exact Aux.icm_const _ _
  case dlet =>
    intro st env l p e ih
    by_cases hc : ALL_DISTINCT (pat_bindings p []) ∧ every_exp (one_con_check env.c) e
    · refine hT (fun s => evaluate s env [e])
        (fun r st' => match r with
          | Rval v => (st',
              match pmatch env.c st'.refs p (HD v) [] with
              | No_match => Rerr (Rraise bind_exn_v)
              | Match_type_error => Rerr (Rabort Rtype_error)
              | Match new_vals => Rval { v := alist_to_ns new_vals, c := nsEmpty })
          | Rerr err => (st', Rerr err)) st _ ?_ (ih hc) ?_ (fun _ => rfl)
      · intro s
        dsimp only
        rw [evaluate_decs, if_pos hc]
        rcases evaluate s env [e] with ⟨_, _ | _⟩ <;> rfl
      · rintro s' (v | e) _
        · exact Aux.icm_congr _ (fun clk => rfl) (Aux.icm_const s'
            (match pmatch env.c s'.refs p (HD v) [] with
              | No_match => Rerr (Rraise bind_exn_v)
              | Match_type_error => Rerr (Rabort Rtype_error)
              | Match new_vals => Rval { v := alist_to_ns new_vals, c := nsEmpty }))
        · exact Aux.icm_const _ _
    · refine Aux.icm_congr _ (fun clk => ?_) (Aux.icm_const st (Rerr (Rabort Rtype_error)))
      rw [evaluate_decs, if_neg hc]
  case dletrec => intro st env l funs; simp only [evaluate_decs]; exact Aux.icm_const _ _
  case dtype =>
    intro st env l tds
    by_cases hc : EVERY check_dup_ctors tds
    · refine Aux.icm_simple (t' := { st with next_type_stamp := st.next_type_stamp + tds.length })
        (r := Rval { v := nsEmpty, c := build_tdefs st.next_type_stamp tds }) (fun clk => ?_)
        (io_events_mono_refl _) (Nat.le_add_right _ _) (Nat.le_refl _) (Nat.le_refl _)
      rw [evaluate_decs, if_pos hc]
    · refine Aux.icm_congr _ (fun clk => ?_) (Aux.icm_const st (Rerr (Rabort Rtype_error)))
      rw [evaluate_decs, if_neg hc]
  case dtabbrev => intro st env l tvs tn t; simp only [evaluate_decs]; exact Aux.icm_const _ _
  case denv =>
    intro st env n
    cases hd : declare_env st.eval_state env with
    | none =>
      refine Aux.icm_congr _ (fun clk => ?_) (Aux.icm_const st (Rerr (Rabort Rtype_error)))
      rw [evaluate_decs, hd]
    | some p =>
      obtain ⟨x, es'⟩ := p
      refine Aux.icm_simple (t' := { st with eval_state := es' })
        (r := Rval { v := nsSing n x, c := nsEmpty }) (fun clk => ?_)
        (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      rw [evaluate_decs, hd]
  case dexn =>
    intro st env l cn ts
    refine Aux.icm_simple (t' := { st with next_exn_stamp := st.next_exn_stamp + 1 })
      (r := Rval { v := nsEmpty, c := nsSing cn (ts.length, ExnStamp st.next_exn_stamp) })
      (fun clk => ?_)
      (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_add_right _ _) (Nat.le_refl _)
    rw [evaluate_decs]
  case dmod =>
    intro st env mn ds ih
    refine hT (fun s => evaluate_decs s env ds)
      (fun r st' => (st', match r with
        | Rval env' => Rval { v := nsLift mn env'.v, c := nsLift mn env'.c }
        | Rerr err => Rerr err)) st _ ?_ ih ?_ (fun _ => rfl)
    · intro s; rw [evaluate_decs]; rfl
    · rintro s' r _; exact Aux.icm_const _ _
  case dlocal =>
    intro st env lds ds ih1 ih2
    refine hT (fun s => evaluate_decs s env lds)
      (fun r st1 => match r with
        | Rval env1 => evaluate_decs st1 (extend_dec_env env1 env) ds
        | Rerr v7 => (st1, Rerr v7)) st _ ?_ ih1 ?_ (fun _ => rfl)
    · intro s
      dsimp only
      rw [Aux.evaluate_decs_Dlocal]
      rcases evaluate_decs s env lds with ⟨_, _ | _⟩ <;> rfl
    · rintro s' (env1 | e) h
      · exact ih2 _ _ h
      · exact Aux.icm_const _ _

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
  have h := h s
  rw [Aux.icm_iff hf] at h
  obtain ⟨-, hc, -, -, -, h⟩ := h
  rcases he : f { s with clock := s.clock + extra } with ⟨s'', r'⟩
  obtain ⟨h1, h2, -, -⟩ := h _ _ _ he
  have hr' := (h2 hr).1 (by omega)
  obtain ⟨rfl, rfl⟩ := h1 hr' hr
  have : s.clock + extra - (s.clock - s'.clock) = s'.clock + extra := by omega
  rw [this]

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
  apply Aux.full_evaluate_ind
  case nil => intro st env s' r h; simp only [evaluate] at h; cases h; rfl
  case cons2 =>
    intro st env e1 e2 es ih1 ih2 s' r h
    rw [Aux.evaluate_cons2] at h
    split at h
    · rename_i st' v1 h1
      split at h
      · rename_i h2
        cases h
        simp only [List.length_cons, ih2 _ _ h1 _ _ h2]
      · cases h
    · cases h
  case lit => intro st env l s' r h; simp only [evaluate] at h; cases h; rfl
  case raise => intro st env e ih s' r h; rw [evaluate] at h; split at h <;> cases h
  case handle =>
    intro st env e pes ih1 ih2 s' r h
    rw [Aux.evaluate_Handle] at h
    split at h
    · rename_i h1
      cases h
      exact ih1 _ _ h1
    · rename_i h1
      split at h
      · rename_i hp; exact ih2 _ _ h1 hp _ _ h
      · cases h
    · cases h
  case con =>
    intro st env cn es ih s' r h
    rw [evaluate] at h
    split at h
    · split at h
      · split at h
        · cases h
        · cases h; rfl
      · cases h
    · cases h
  case var =>
    intro st env n s' r h
    rw [evaluate] at h
    split at h <;> cases h
    rfl
  case func => intro st env x e s' r h; simp only [evaluate] at h; cases h; rfl
  case app =>
    intro st env o es ih1 ih2 ih3 ih4 s' r h
    rw [Aux.evaluate_App] at h
    split at h
    · rename_i st' vs h1
      split at h
      · rename_i ho
        split at h
        · rename_i hop
          split at h
          · cases h
          · rename_i hc
            exact ih2 _ _ _ _ h1 ho hop hc _ _ h
        · cases h
      · rename_i ho
        split at h
        · cases h
        · cases h
        · cases h; rfl
        · rename_i hd
          split at h
          · rename_i hop
            split at h
            · cases h
            · rename_i hc
              split at h
              · rename_i h2
                split at h
                · cases h
                · cases h
                  exact ih3 _ _ _ _ _ h1 ho hd hop hc _ _ h2
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
        · simp only [Prod.mk.injEq, list_result_eq_Rval] at h
          obtain ⟨_, v, rfl, _⟩ := h
          rfl
    · rename_i hn
      exact absurd h (hn _ _)
  case log =>
    intro st env l e1 e2 ih1 ih2 s' r h
    rw [Aux.evaluate_Log] at h
    split at h
    · rename_i h1
      split at h
      · cases h
      · rename_i hl; exact ih2 _ _ _ h1 hl _ _ h
      · cases h; rfl
    · cases h
  case ite =>
    intro st env e1 e2 e3 ih1 ih2 s' r h
    rw [Aux.evaluate_If] at h
    split at h
    · rename_i h1
      split at h
      · cases h
      · rename_i hl; exact ih2 _ _ _ h1 hl _ _ h
    · cases h
  case mat =>
    intro st env e pes ih1 ih2 s' r h
    rw [Aux.evaluate_Mat] at h
    split at h
    · rename_i h1
      split at h
      · rename_i hp; exact ih2 _ _ h1 hp _ _ h
      · cases h
    · cases h
  case letc =>
    intro st env xo e1 e2 ih1 ih2 s' r h
    rw [Aux.evaluate_Let] at h
    split at h
    · rename_i h1
      exact ih2 _ _ h1 _ _ h
    · cases h
  case letrec =>
    intro st env funs e ih s' r h
    rw [evaluate] at h
    split at h
    · rename_i hd; exact ih hd _ _ h
    · cases h
  case tannot => intro st env e t ih s' r h; rw [evaluate] at h; exact ih _ _ h
  case lannot => intro st env e l ih s' r h; rw [evaluate] at h; exact ih _ _ h
  case mnil => intro st env v v' s' r h; rw [evaluate_match] at h; cases h
  case mcons =>
    intro st env v p e pes v' ih1 ih2 s' r h
    rw [evaluate_match] at h
    split at h
    · rename_i hd
      split at h
      · rename_i hp; exact ih1 hd hp _ _ h
      · cases h
      · rename_i hp; exact ih2 _ hd hp _ _ h
    · cases h
  all_goals intros; trivial

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
  rw [Aux.icm_iff hf] at h
  obtain ⟨-, hc, -, -, -, h⟩ := h
  refine ⟨ck1 + (s.clock - s'.clock), ?_⟩
  rcases he : f { s with clock := ck1 + (s.clock - s'.clock) } with ⟨s'', r'⟩
  obtain ⟨h1, h2, -, -⟩ := h _ _ _ he
  have hr' := (h2 hr).1 (by omega)
  obtain ⟨rfl, rfl⟩ := h1 hr' hr
  have : ck1 + (s.clock - s'.clock) - (s.clock - s'.clock) = ck1 := by omega
  rw [this]

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
  rintro h ⟨hf, hc0, hr, hk⟩
  rw [Aux.icm_iff hf] at h
  obtain ⟨-, hc, -, -, -, h⟩ := h
  rcases he : f { s with clock := k } with ⟨s'', r'⟩
  obtain ⟨h1, h2, -, h4⟩ := h _ _ _ he
  have hr' : r' = Rerr (Rabort Rtimeout_error) := by
    apply Classical.byContradiction
    intro hn
    have := (h2 hr).2 hn
    omega
  subst hr'
  exact ⟨s'', rfl, h4 (by omega)⟩

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
  | cons p ps ih =>
    simp only [can_pmatch_all, EVERY, ih]
    split
    · rename_i h; simp [h]
    · rename_i h; simp [h]

end

end CmlTS
