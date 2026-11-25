import CmlTS.Ast
import CmlTS.Evaluate
import CmlTS.Namespace
import CmlTS.NamespaceProps
import CmlTS.SemanticPrimitives
import CmlTS.SemanticPrimitivesProps
/-
  Translation of HOL4 theory `evaluateProps` (evaluatePropsScript.sml): definitions.
-/
set_option autoImplicit false

namespace CmlTS
open Classical

/- HOL4:
Definition call_FFI_rel_def:
  call_FFI_rel s1 s2 <=> ?n conf bytes t. call_FFI s1 n conf bytes = FFI_return s2 t
End -/
def call_FFI_rel {ffiT : Type} (s1 s2 : ffi_state ffiT) : Prop :=
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
def io_events_mono {ffiT : Type} (s1 s2 : ffi_state ffiT) : Prop :=
  s1.io_events <+: s2.io_events ∧
  (s2.io_events = s1.io_events → s2 = s1)

/- HOL4:
Theorem io_events_mono_trans:
   io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 ⇒
   io_events_mono ffi1 ffi3 -/
theorem io_events_mono_trans {ffiT : Type} (ffi1 ffi2 ffi3 : ffi_state ffiT) :
    io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 →
    io_events_mono ffi1 ffi3 := by sorry

/- HOL4:
Theorem call_FFI_rel_io_events_mono:
   ∀s1 s2.
   RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2 -/
theorem call_FFI_rel_io_events_mono {ffiT : Type} :
    ∀ s1 s2 : ffi_state ffiT,
      RTC call_FFI_rel s1 s2 → io_events_mono s1 s2 := by sorry

/- HOL4:
Theorem io_events_mono_refl[simp]:
   io_events_mono ffi ffi -/
theorem io_events_mono_refl {ffiT : Type} (ffi : ffi_state ffiT) :
    io_events_mono ffi ffi := by sorry

/- HOL4:
Theorem do_app_call_FFI_rel:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi' -/
theorem do_app_call_FFI_rel {ffiT : Type} (r : List (store_v val)) (ffi : ffi_state ffiT)
    (op : CmlTS.op) (vs : List val) (r' : List (store_v val)) (ffi' : ffi_state ffiT)
    (res : result val val) :
    do_app (r, ffi) op vs = some ((r', ffi'), res) →
    RTC call_FFI_rel ffi ffi' := by sorry

/- HOL4:
Theorem do_app_io_events_mono:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi' -/
theorem do_app_io_events_mono {ffiT : Type} (r : List (store_v val)) (ffi : ffi_state ffiT)
    (op : CmlTS.op) (vs : List val) (r' : List (store_v val)) (ffi' : ffi_state ffiT)
    (res : result val val) :
    do_app (r, ffi) op vs = some ((r', ffi'), res) → io_events_mono ffi ffi' := by sorry

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
def is_clock_io_mono {ffiT α β : Type} (f : state ffiT → state ffiT × result α β)
    (s : state ffiT) : Prop :=
  match f s with
  | (s', r) =>
    io_events_mono s.ffi s'.ffi
    ∧ s'.clock ≤ s.clock
    ∧ s.next_type_stamp ≤ s'.next_type_stamp
    ∧ s.next_exn_stamp ≤ s'.next_exn_stamp
    ∧ s.refs.length ≤ s'.refs.length
    ∧ (∀ clk : Nat,
        match f { s with clock := clk } with
        | (s'', r') =>
          (¬ (r' = .Rerr (.Rabort .Rtimeout_error))
            → ¬ (r = .Rerr (.Rabort .Rtimeout_error))
            → r' = r
              ∧ s'' = { s' with clock := clk - (s.clock - s'.clock) })
          ∧ (¬ (r = .Rerr (.Rabort .Rtimeout_error))
              → (clk ≥ s.clock - s'.clock
                  ↔ ¬ (r' = .Rerr (.Rabort .Rtimeout_error))))
          ∧ (¬ (r' = .Rerr (.Rabort .Rtimeout_error))
              → clk ≤ s.clock
              → ¬ (r = .Rerr (.Rabort .Rtimeout_error)))
          ∧ (clk ≤ s.clock → io_events_mono s''.ffi s'.ffi))

/- HOL4:
Theorem is_clock_io_mono_cong:
  s = t ==>
  (!s. s.eval_state = t.eval_state /\ s.refs = t.refs /\ s.ffi = t.ffi ==>
    f s = g s) ==>
  (is_clock_io_mono f s <=> is_clock_io_mono g t) -/
theorem is_clock_io_mono_cong {ffiT α β : Type} (s t : state ffiT)
    (f g : state ffiT → state ffiT × result α β) :
    s = t →
    (∀ s : state ffiT, s.eval_state = t.eval_state ∧ s.refs = t.refs ∧ s.ffi = t.ffi →
      f s = g s) →
    (is_clock_io_mono f s ↔ is_clock_io_mono g t) := by sorry

/- HOL4:
Theorem is_clock_io_mono_return:
   is_clock_io_mono (\s. (s,Rval r)) s -/
theorem is_clock_io_mono_return {ffiT α β : Type} (r : α) (s : state ffiT) :
    is_clock_io_mono (fun s => (s, (.Rval r : result α β))) s := by sorry

/- HOL4:
Theorem is_clock_io_mono_err:
   is_clock_io_mono (\s. (s,Rerr r)) s -/
theorem is_clock_io_mono_err {ffiT α β : Type} (r : error_result β) (s : state ffiT) :
    is_clock_io_mono (fun s => (s, (.Rerr r : result α β))) s := by sorry

/- HOL4:
Theorem pair_CASE_eq_forall:
   (case x of (a, b) => P a b) = (!a b. x = (a, b) ==> P a b) -/
theorem pair_CASE_eq_forall {α β : Type} (x : α × β) (P : α → β → Prop) :
    (match x with | (a, b) => P a b) ↔ (∀ a b, x = (a, b) → P a b) := by sorry

/- HOL4:
Theorem is_clock_io_mono_bind:
   is_clock_io_mono f s /\ (!s' r. f s = (s', r)
        ==> is_clock_io_mono (g r) s')
    /\ (!s'. g (Rerr (Rabort Rtimeout_error)) s'
        = (s', Rerr (Rabort Rtimeout_error)))
    ==> is_clock_io_mono (\s. case f s of (s', r) => g r s') s -/
theorem is_clock_io_mono_bind {ffiT α β γ δ : Type}
    (f : state ffiT → state ffiT × result α β) (s : state ffiT)
    (g : result α β → state ffiT → state ffiT × result γ δ) :
    is_clock_io_mono f s ∧
    (∀ s' r, f s = (s', r) → is_clock_io_mono (g r) s') ∧
    (∀ s', g (.Rerr (.Rabort .Rtimeout_error)) s'
      = (s', .Rerr (.Rabort .Rtimeout_error))) →
    is_clock_io_mono (fun s => match f s with | (s', r) => g r s') s := by sorry

/- HOL4:
Definition adj_clock_def:
  adj_clock inc dec s = (s with clock := ((s.clock + inc) - dec))
End -/
def adj_clock {ffiT : Type} (inc dec : Nat) (s : state ffiT) : state ffiT :=
  { s with clock := (s.clock + inc) - dec }

/- HOL4:
Theorem is_clock_io_mono_check:
   (~ (s.clock = 0) ==>
        is_clock_io_mono (\s. f (adj_clock 1 0 s)) (dec_clock s))
    ==> is_clock_io_mono (\s. if s.clock = 0
        then (s,Rerr (Rabort Rtimeout_error)) else f s) s -/
theorem is_clock_io_mono_check {ffiT α β : Type} (s : state ffiT)
    (f : state ffiT → state ffiT × result α β) :
    (¬ (s.clock = 0) →
      is_clock_io_mono (fun s => f (adj_clock 1 0 s)) (dec_clock s)) →
    is_clock_io_mono (fun s =>
      if s.clock = 0 then (s, .Rerr (.Rabort .Rtimeout_error)) else f s) s := by sorry

/- HOL4:
Theorem dec_inc_clock:
  dec_clock (adj_clock 1 0 s) = s -/
theorem dec_inc_clock {ffiT : Type} (s : state ffiT) :
    dec_clock (adj_clock 1 0 s) = s := by sorry

/- HOL4:
Theorem do_app_refs_length:
   do_app refs_ffi op vs = SOME res ==>
   LENGTH (FST refs_ffi) <= LENGTH (FST (FST res)) -/
theorem do_app_refs_length {ffiT : Type} (refs_ffi : List (store_v val) × ffi_state ffiT)
    (op : CmlTS.op) (vs : List val)
    (res : (List (store_v val) × ffi_state ffiT) × result val val) :
    do_app refs_ffi op vs = some res →
    refs_ffi.1.length ≤ res.1.1.length := by sorry

/- HOL4:
Theorem is_clock_io_mono_do_app_simple:
  ! xs (st:'ffi state).
   is_clock_io_mono (\st'.
    case do_app (st'.refs, st'.ffi) op xs of
      NONE => (st', Rerr (Rabort Rtype_error))
    | SOME ((refs,ffi),r) =>
      (st' with<| refs := refs; ffi := ffi |>, list_result r)) st -/
theorem is_clock_io_mono_do_app_simple {ffiT : Type} (op : CmlTS.op) :
    ∀ (xs : List val) (st : state ffiT),
      is_clock_io_mono (fun st' =>
        match do_app (st'.refs, st'.ffi) op xs with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some ((refs, ffi), r) =>
          ({ st' with refs := refs, ffi := ffi }, list_result r)) st := by sorry

/- HOL4:
Theorem is_clock_io_mono_evaluate:
   (!(s : 'ffi state) env es. is_clock_io_mono (\s. evaluate s env es) s) /\
   (!(s : 'ffi state) env v pes err_v.
        is_clock_io_mono (\s. evaluate_match s env v pes err_v) s) /\
   (!(s : 'ffi state) env ds.
        is_clock_io_mono (\s. evaluate_decs s env ds) s) -/
theorem is_clock_io_mono_evaluate {ffiT : Type} :
    (∀ (s : state ffiT) env es, is_clock_io_mono (fun s => evaluate s env es) s) ∧
    (∀ (s : state ffiT) env v pes err_v,
      is_clock_io_mono (fun s => evaluate_match s env v pes err_v) s) ∧
    (∀ (s : state ffiT) env ds,
      is_clock_io_mono (fun s => evaluate_decs s env ds) s) := by sorry

/- HOL4:
Theorem is_clock_io_mono_evaluate_decs:
  !s e p. is_clock_io_mono (\s. evaluate_decs s e p) s -/
theorem is_clock_io_mono_evaluate_decs {ffiT : Type} :
    ∀ (s : state ffiT) e p, is_clock_io_mono (fun s => evaluate_decs s e p) s := by sorry

/- HOL4:
Theorem is_clock_io_mono_extra:
   (!s. is_clock_io_mono f s)
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> f (s with clock := s.clock + extra)
        = (s' with clock := s'.clock + extra,r) -/
theorem is_clock_io_mono_extra {ffiT α β : Type} (f : state ffiT → state ffiT × result α β)
    (s s' : state ffiT) (r : result α β) (extra : Nat) :
    (∀ s, is_clock_io_mono f s) →
    f s = (s', r) ∧ ¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
    f { s with clock := s.clock + extra }
      = ({ s' with clock := s'.clock + extra }, r) := by sorry

/- HOL4:
Theorem list_result_eq_Rval[simp]:
  list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v -/
theorem list_result_eq_Rval {α β : Type} (r : result α β) (r' : List α) :
    list_result r = .Rval r' ↔ ∃ v, r' = [v] ∧ r = .Rval v := by sorry

/- HOL4:
Theorem evaluate_length:
   (∀(s:'ffi state) e p s' r. evaluate s e p = (s',Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e v p er s' r. evaluate_match s e v p er = (s',Rval r) ⇒ LENGTH r = 1) ∧
   (∀(s:'ffi state) e ds s' r. evaluate_decs s e ds = (s',Rval r) ⇒ T) -/
theorem evaluate_length {ffiT : Type} :
    (∀ (s : state ffiT) e p s' r, evaluate s e p = (s', .Rval r) → r.length = p.length) ∧
    (∀ (s : state ffiT) e v p er s' r,
      evaluate_match s e v p er = (s', .Rval r) → r.length = 1) ∧
    (∀ (s : state ffiT) e ds s' r, evaluate_decs s e ds = (s', .Rval r) → True) := by sorry

/- HOL4:
Theorem is_clock_io_mono_set_clock:
   is_clock_io_mono f s
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> ?ck0. f (s with clock := ck0) = (s' with clock := ck1, r) -/
theorem is_clock_io_mono_set_clock {ffiT α β : Type}
    (f : state ffiT → state ffiT × result α β)
    (s s' : state ffiT) (r : result α β) (ck1 : Nat) :
    is_clock_io_mono f s →
    f s = (s', r) ∧ ¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
    ∃ ck0, f { s with clock := ck0 } = ({ s' with clock := ck1 }, r) := by sorry

/- HOL4:
Theorem is_clock_io_mono_minimal:
   is_clock_io_mono f s
    ==> f s = (s', r) /\ s'.clock = 0 /\ r <> Rerr (Rabort Rtimeout_error)
        /\ s.clock > k
    ==> (?s''. f (s with clock := k) = (s'', Rerr (Rabort Rtimeout_error)) /\
               io_events_mono s''.ffi s'.ffi) -/
theorem is_clock_io_mono_minimal {ffiT α β : Type}
    (f : state ffiT → state ffiT × result α β)
    (s s' : state ffiT) (r : result α β) (k : Nat) :
    is_clock_io_mono f s →
    f s = (s', r) ∧ s'.clock = 0 ∧ r ≠ .Rerr (.Rabort .Rtimeout_error)
      ∧ s.clock > k →
    (∃ s'', f { s with clock := k } = (s'', .Rerr (.Rabort .Rtimeout_error)) ∧
      io_events_mono s''.ffi s'.ffi) := by sorry

/- HOL4:
Theorem can_pmatch_all_EVERY:
  can_pmatch_all envC refs ps v <=>
  EVERY (\p. pmatch envC refs p v [] <> Match_type_error) ps -/
theorem can_pmatch_all_EVERY (envC : env_ctor) (refs : List (store_v val)) (ps : List pat)
    (v : val) :
    can_pmatch_all envC refs ps v ↔
    EVERY (fun p => pmatch envC refs p v [] ≠ .Match_type_error) ps := by sorry

end CmlTS
