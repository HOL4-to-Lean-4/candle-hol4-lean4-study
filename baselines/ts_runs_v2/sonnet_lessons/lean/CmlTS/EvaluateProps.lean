import CmlTS.Ast
import CmlTS.Evaluate
import CmlTS.Namespace
import CmlTS.NamespaceProps
import CmlTS.SemanticPrimitives
import CmlTS.SemanticPrimitivesProps

/-!
# evaluateProps (HOL4 theory `evaluateProps`): properties of the operational semantics

Definitions of this theory (the theorems are for stage 2).
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   Definition call_FFI_rel_def:
     call_FFI_rel s1 s2 <=> ?n conf bytes t. call_FFI s1 n conf bytes = FFI_return s2 t
   End -/
def call_FFI_rel {α : Type u} (s1 s2 : ffi_state α) : Prop :=
  ∃ n conf bytes t, call_FFI s1 n conf bytes = .FFI_return s2 t

/- HOL4:
   Definition dest_IO_event_def[simp]:
     dest_IO_event (IO_event s c b) = (s,c,b)
   End -/
def dest_IO_event : io_event → ffiname × List word8 × List (word8 × word8)
  | .IO_event s c b => (s, c, b)

/- HOL4:
   Definition io_events_mono_def:
     io_events_mono s1 s2 ⇔
       s1.io_events ≼ s2.io_events ∧
       (s2.io_events = s1.io_events ⇒ s2 = s1)
   End -/
def io_events_mono {α : Type u} (s1 s2 : ffi_state α) : Prop :=
  s1.io_events ≼ s2.io_events ∧ (s2.io_events = s1.io_events → s2 = s1)

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
def is_clock_io_mono {α : Type u} {β : Type v} {γ : Type w}
    (f : state α → state α × result β γ) (s : state α) : Prop :=
  match f s with
  | (s', r) =>
    io_events_mono s.ffi s'.ffi
    ∧ s'.clock ≤ s.clock
    ∧ s.next_type_stamp ≤ s'.next_type_stamp
    ∧ s.next_exn_stamp ≤ s'.next_exn_stamp
    ∧ LENGTH s.refs ≤ LENGTH s'.refs
    ∧ (∀ clk, match f { s with clock := clk } with
        | (s'', r') =>
          (¬ (r' = .Rerr (.Rabort .Rtimeout_error))
            → ¬ (r = .Rerr (.Rabort .Rtimeout_error))
            → r' = r ∧ s'' = { s' with clock := clk - (s.clock - s'.clock) })
          ∧ (¬ (r = .Rerr (.Rabort .Rtimeout_error))
            → (clk ≥ s.clock - s'.clock ↔ ¬ (r' = .Rerr (.Rabort .Rtimeout_error))))
          ∧ (¬ (r' = .Rerr (.Rabort .Rtimeout_error))
            → clk ≤ s.clock
            → ¬ (r = .Rerr (.Rabort .Rtimeout_error)))
          ∧ (clk ≤ s.clock → io_events_mono s''.ffi s'.ffi))

/- HOL4:
   Definition adj_clock_def:
     adj_clock inc dec s = (s with clock := ((s.clock + inc) - dec))
   End -/
def adj_clock {α : Type u} (inc dec : Nat) (s : state α) : state α :=
  { s with clock := (s.clock + inc) - dec }

/- HOL4: io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 ⇒
   io_events_mono ffi1 ffi3 -/
theorem io_events_mono_trans {α : Type} (ffi1 ffi2 ffi3 : ffi_state α) :
    io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 → io_events_mono ffi1 ffi3 := by
  sorry

/- HOL4: ∀s1 s2.
   RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2 -/
theorem call_FFI_rel_io_events_mono {α : Type} :
    ∀ s1 s2 : ffi_state α, RTC call_FFI_rel s1 s2 → io_events_mono s1 s2 := by
  sorry

/- HOL4: io_events_mono ffi ffi -/
theorem io_events_mono_refl {α : Type} (ffi : ffi_state α) : io_events_mono ffi ffi := by
  sorry

/- HOL4: do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi' -/
theorem do_app_call_FFI_rel {α : Type} (r : List (store_v Value)) (ffi : ffi_state α) (o : op)
    (vs : List Value) (r' : List (store_v Value)) (ffi' : ffi_state α)
    (res : result Value Value) :
    do_app (r, ffi) o vs = some ((r', ffi'), res) → RTC call_FFI_rel ffi ffi' := by
  sorry

/- HOL4: do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi' -/
theorem do_app_io_events_mono {α : Type} (r : List (store_v Value)) (ffi : ffi_state α) (o : op)
    (vs : List Value) (r' : List (store_v Value)) (ffi' : ffi_state α)
    (res : result Value Value) :
    do_app (r, ffi) o vs = some ((r', ffi'), res) → io_events_mono ffi ffi' := by
  sorry

/- HOL4: s = t ==>
  (!s. s.eval_state = t.eval_state /\ s.refs = t.refs /\ s.ffi = t.ffi ==>
    f s = g s) ==>
  (is_clock_io_mono f s <=> is_clock_io_mono g t) -/
theorem is_clock_io_mono_cong {α β γ : Type} (f g : state α → state α × result β γ)
    (s t : state α) :
    s = t →
    (∀ s : state α, s.eval_state = t.eval_state ∧ s.refs = t.refs ∧ s.ffi = t.ffi → f s = g s) →
    (is_clock_io_mono f s ↔ is_clock_io_mono g t) := by
  sorry

/- HOL4: is_clock_io_mono (\s. (s,Rval r)) s -/
theorem is_clock_io_mono_return {α β γ : Type} (r : β) (s : state α) :
    is_clock_io_mono (fun s : state α => (s, (result.Rval r : result β γ))) s := by
  sorry

/- HOL4: is_clock_io_mono (\s. (s,Rerr r)) s -/
theorem is_clock_io_mono_err {α β γ : Type} (r : error_result γ) (s : state α) :
    is_clock_io_mono (fun s : state α => (s, (result.Rerr r : result β γ))) s := by
  sorry

/- HOL4: (case x of (a, b) => P a b) = (!a b. x = (a, b) ==> P a b) -/
theorem pair_CASE_eq_forall {A B : Type} (x : A × B) (P : A → B → Prop) :
    (match x with | (a, b) => P a b) = (∀ a b, x = (a, b) → P a b) := by
  sorry

/- HOL4: is_clock_io_mono f s /\ (!s' r. f s = (s', r)
        ==> is_clock_io_mono (g r) s')
    /\ (!s'. g (Rerr (Rabort Rtimeout_error)) s'
        = (s', Rerr (Rabort Rtimeout_error)))
    ==> is_clock_io_mono (\s. case f s of (s', r) => g r s') s -/
theorem is_clock_io_mono_bind {α β γ δ ε : Type} (f : state α → state α × result β γ)
    (g : result β γ → state α → state α × result δ ε) (s : state α) :
    is_clock_io_mono f s ∧
      (∀ (s' : state α) (r : result β γ), f s = (s', r) → is_clock_io_mono (g r) s') ∧
      (∀ s' : state α, g (.Rerr (.Rabort .Rtimeout_error)) s' = (s', .Rerr (.Rabort .Rtimeout_error)))
    → is_clock_io_mono (fun s => match f s with | (s', r) => g r s') s := by
  sorry

/- HOL4: (~ (s.clock = 0) ==>
        is_clock_io_mono (\s. f (adj_clock 1 0 s)) (dec_clock s))
    ==> is_clock_io_mono (\s. if s.clock = 0
        then (s,Rerr (Rabort Rtimeout_error)) else f s) s -/
theorem is_clock_io_mono_check {α β γ : Type} (f : state α → state α × result β γ)
    (s : state α) :
    (¬ (s.clock = 0) → is_clock_io_mono (fun s => f (adj_clock 1 0 s)) (dec_clock s)) →
    is_clock_io_mono (fun s => if s.clock = 0 then (s, .Rerr (.Rabort .Rtimeout_error)) else f s) s := by
  sorry

/- HOL4: dec_clock (adj_clock 1 0 s) = s -/
theorem dec_inc_clock {α : Type} (s : state α) : dec_clock (adj_clock 1 0 s) = s := by
  sorry

/- HOL4: do_app refs_ffi op vs = SOME res ==>
   LENGTH (FST refs_ffi) <= LENGTH (FST (FST res)) -/
theorem do_app_refs_length {α : Type} (refs_ffi : List (store_v Value) × ffi_state α) (o : op)
    (vs : List Value) (res : (List (store_v Value) × ffi_state α) × result Value Value) :
    do_app refs_ffi o vs = some res → LENGTH (FST refs_ffi) ≤ LENGTH (FST (FST res)) := by
  sorry

/- HOL4: ! xs (st:'ffi state).
   is_clock_io_mono (\st'.
    case do_app (st'.refs, st'.ffi) op xs of
      NONE => (st', Rerr (Rabort Rtype_error))
    | SOME ((refs,ffi),r) =>
      (st' with<| refs := refs; ffi := ffi |>, list_result r)) st -/
theorem is_clock_io_mono_do_app_simple {α : Type} (o : op) :
    ∀ (xs : List Value) (st : state α),
      is_clock_io_mono (fun st' : state α =>
        match do_app (st'.refs, st'.ffi) o xs with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some ((refs, ffi), r) => ({ st' with refs := refs, ffi := ffi }, list_result r)) st := by
  sorry

/- HOL4: (!(s : 'ffi state) env es. is_clock_io_mono (\s. evaluate s env es) s) /\
   (!(s : 'ffi state) env v pes err_v.
        is_clock_io_mono (\s. evaluate_match s env v pes err_v) s) /\
   (!(s : 'ffi state) env ds.
        is_clock_io_mono (\s. evaluate_decs s env ds) s) -/
theorem is_clock_io_mono_evaluate {α : Type} :
    (∀ (s : state α) (env : sem_env Value) (es : List exp),
        is_clock_io_mono (fun s => evaluate s env es) s) ∧
    (∀ (s : state α) (env : sem_env Value) (v : Value) (pes : List (pat × exp)) (err_v : Value),
        is_clock_io_mono (fun s => evaluate_match s env v pes err_v) s) ∧
    (∀ (s : state α) (env : sem_env Value) (ds : List dec),
        is_clock_io_mono (fun s => evaluate_decs s env ds) s) := by
  sorry

/- HOL4: !s e p. is_clock_io_mono (\s. evaluate_decs s e p) s -/
theorem is_clock_io_mono_evaluate_decs {α : Type} :
    ∀ (s : state α) (e : sem_env Value) (p : List dec),
      is_clock_io_mono (fun s => evaluate_decs s e p) s := by
  sorry

/- HOL4: (!s. is_clock_io_mono f s)
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> f (s with clock := s.clock + extra)
        = (s' with clock := s'.clock + extra,r) -/
theorem is_clock_io_mono_extra {α β γ : Type} (f : state α → state α × result β γ)
    (s s' : state α) (r : result β γ) (extra : Nat) :
    (∀ s : state α, is_clock_io_mono f s) →
    f s = (s', r) ∧ ¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
    f { s with clock := s.clock + extra } = ({ s' with clock := s'.clock + extra }, r) := by
  sorry

/- HOL4: list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v -/
theorem list_result_eq_Rval {α β : Type} (r : result α β) (r' : List α) :
    list_result r = .Rval r' ↔ ∃ v, r' = [v] ∧ r = .Rval v := by
  sorry

/- HOL4: (∀(s:'ffi state) e p s' r. evaluate s e p = (s',Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e v p er s' r. evaluate_match s e v p er = (s',Rval r) ⇒ LENGTH r = 1) ∧
   (∀(s:'ffi state) e ds s' r. evaluate_decs s e ds = (s',Rval r) ⇒ T) -/
theorem evaluate_length {α : Type} :
    (∀ (s : state α) (e : sem_env Value) (p : List exp) (s' : state α) (r : List Value),
        evaluate s e p = (s', .Rval r) → LENGTH r = LENGTH p) ∧
    (∀ (s : state α) (e : sem_env Value) (v : Value) (p : List (pat × exp)) (er : Value)
        (s' : state α) (r : List Value),
        evaluate_match s e v p er = (s', .Rval r) → LENGTH r = 1) ∧
    (∀ (s : state α) (e : sem_env Value) (ds : List dec) (s' : state α) (r : sem_env Value),
        evaluate_decs s e ds = (s', .Rval r) → True) := by
  sorry

/- HOL4: is_clock_io_mono f s
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> ?ck0. f (s with clock := ck0) = (s' with clock := ck1, r) -/
theorem is_clock_io_mono_set_clock {α β γ : Type} (f : state α → state α × result β γ)
    (s s' : state α) (r : result β γ) (ck1 : Nat) :
    is_clock_io_mono f s →
    f s = (s', r) ∧ ¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
    ∃ ck0, f { s with clock := ck0 } = ({ s' with clock := ck1 }, r) := by
  sorry

/- HOL4: is_clock_io_mono f s
    ==> f s = (s', r) /\ s'.clock = 0 /\ r <> Rerr (Rabort Rtimeout_error)
        /\ s.clock > k
    ==> (?s''. f (s with clock := k) = (s'', Rerr (Rabort Rtimeout_error)) /\
               io_events_mono s''.ffi s'.ffi) -/
theorem is_clock_io_mono_minimal {α β γ : Type} (f : state α → state α × result β γ)
    (s s' : state α) (r : result β γ) (k : Nat) :
    is_clock_io_mono f s →
    f s = (s', r) ∧ s'.clock = 0 ∧ r ≠ .Rerr (.Rabort .Rtimeout_error) ∧ s.clock > k →
    ∃ s'' : state α, f { s with clock := k } = (s'', .Rerr (.Rabort .Rtimeout_error)) ∧
      io_events_mono s''.ffi s'.ffi := by
  sorry

/- HOL4: can_pmatch_all envC refs ps v <=>
  EVERY (\p. pmatch envC refs p v [] <> Match_type_error) ps -/
theorem can_pmatch_all_EVERY (envC : Namespace modN conN (Nat × stamp))
    (refs : List (store_v Value)) (ps : List pat) (v : Value) :
    can_pmatch_all envC refs ps v ↔
      EVERY (fun p => pmatch envC refs p v [] ≠ .Match_type_error) ps := by
  sorry

end
