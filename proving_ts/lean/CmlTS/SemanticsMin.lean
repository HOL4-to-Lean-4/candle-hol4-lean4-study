import CmlTS.Evaluate
import CmlTS.LprefixLub

/-
HOL4 theory `semantics_min` (semantics_minScript.sml).
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {ffi : Type}

/- HOL4:
Definition evaluate_prog_with_clock_def:
  evaluate_prog_with_clock st env k prog =
    let (st',r) =
      evaluate_decs (st with clock := k) env prog
    in (st'.ffi,r)
End -/
def evaluate_prog_with_clock (st : state ffi) (env : sem_env value) (k : Nat)
    (prog : List dec) : ffi_state ffi × result (sem_env value) value :=
  let (st', r) := evaluate_decs { st with clock := k } env prog
  (st'.ffi, r)

/- HOL4:
Definition semantics_prog_def:
  (semantics_prog st env prog (Terminate outcome io_list) ⇔
    (* there is a clock for which evaluation terminates, either internally or via
       FFI, and the accumulated io events match the given io_list *)
    (?k ffi r.
      evaluate_prog_with_clock st env k prog = (ffi,r) ∧
      (case r of
       | Rerr (Rabort (Rffi_error outcome')) =>
         outcome = FFI_outcome (outcome')
       | r => r ≠ Rerr (Rabort Rtimeout_error) ∧ outcome = Success) ∧
      (io_list = ffi.io_events) ∧
      (r ≠ Rerr (Rabort Rtype_error)))) ∧
  (semantics_prog st env prog (Diverge io_trace) ⇔
    (* for all clocks, evaluation times out *)
    (!k. ?ffi.
      (evaluate_prog_with_clock st env k prog =
          (ffi, Rerr (Rabort Rtimeout_error)))) ∧
    (* the io_trace is the least upper bound of the set of traces
       produced for each clock *)
     lprefix_lub
       (IMAGE
         (λk. fromList (FST (evaluate_prog_with_clock st env k prog)).io_events)
         UNIV)
       io_trace) ∧
  (semantics_prog st env prog Fail ⇔
    (* there is a clock for which evaluation produces a runtime type error *)
    ∃k.
      SND(evaluate_prog_with_clock st env k prog) = Rerr (Rabort Rtype_error))
End -/
def semantics_prog (st : state ffi) (env : sem_env value) (prog : List dec) : behaviour → Prop
  | Terminate outcome io_list =>
    ∃ (k : Nat) (ffi' : ffi_state ffi) (r : result (sem_env value) value),
      evaluate_prog_with_clock st env k prog = (ffi', r) ∧
      (match r with
       | Rerr (Rabort (Rffi_error outcome')) => outcome = FFI_outcome outcome'
       | r => r ≠ Rerr (Rabort Rtimeout_error) ∧ outcome = Success) ∧
      io_list = ffi'.io_events ∧
      r ≠ Rerr (Rabort Rtype_error)
  | Diverge io_trace =>
    (∀ k : Nat, ∃ ffi' : ffi_state ffi,
      evaluate_prog_with_clock st env k prog = (ffi', Rerr (Rabort Rtimeout_error))) ∧
    lprefix_lub
      (IMAGE (fun k => fromList (evaluate_prog_with_clock st env k prog).1.io_events) UNIV)
      io_trace
  | Fail => ∃ k : Nat, (evaluate_prog_with_clock st env k prog).2 = Rerr (Rabort Rtype_error)

end

end CmlTS
