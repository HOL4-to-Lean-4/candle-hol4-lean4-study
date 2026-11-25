import CmlTS.Evaluate
import CmlTS.LprefixLub

/-!
# semantics_min (HOL4 theory `semantics_min`)

Minimized version of semanticsScript.sml for type soundness.
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   Definition evaluate_prog_with_clock_def:
     evaluate_prog_with_clock st env k prog =
       let (st',r) =
         evaluate_decs (st with clock := k) env prog
       in (st'.ffi,r)
   End -/
def evaluate_prog_with_clock {α : Type u} (st : state α) (env : sem_env Value) (k : Nat)
    (prog : List dec) : ffi_state α × result (sem_env Value) Value :=
  match evaluate_decs { st with clock := k } env prog with
  | (st', r) => (st'.ffi, r)

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
def semantics_prog {α : Type u} (st : state α) (env : sem_env Value) (prog : List dec) :
    behaviour → Prop
  | .Terminate outcome io_list =>
    ∃ k ffi r,
      evaluate_prog_with_clock st env k prog = (ffi, r) ∧
      (match r with
       | .Rerr (.Rabort (.Rffi_error outcome')) => outcome = .FFI_outcome outcome'
       | r => r ≠ .Rerr (.Rabort .Rtimeout_error) ∧ outcome = .Success) ∧
      io_list = ffi.io_events ∧
      r ≠ .Rerr (.Rabort .Rtype_error)
  | .Diverge io_trace =>
    (∀ k, ∃ ffi,
      evaluate_prog_with_clock st env k prog = (ffi, .Rerr (.Rabort .Rtimeout_error))) ∧
    lprefix_lub
      (IMAGE (fun k => fromList (FST (evaluate_prog_with_clock st env k prog)).io_events) UNIV)
      io_trace
  | .Fail =>
    ∃ k, SND (evaluate_prog_with_clock st env k prog) = .Rerr (.Rabort .Rtype_error)

end
