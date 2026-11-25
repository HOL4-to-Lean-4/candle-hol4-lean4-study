import CmlTS.Misc
import CmlTS.Mlstring
/-
  Translation of HOL4 theory `ffi` (ffiScript.sml).
-/
set_option autoImplicit false

namespace CmlTS
open Classical

/- HOL4:
Datatype:
  ffi_outcome = FFI_failed | FFI_diverged
End -/
inductive ffi_outcome
  | FFI_failed | FFI_diverged
  deriving DecidableEq, Inhabited

export ffi_outcome (FFI_failed FFI_diverged)

/- HOL4:
Datatype:
  oracle_result = Oracle_return 'ffi (word8 list) | Oracle_final ffi_outcome
End -/
inductive oracle_result (ffi : Type)
  | Oracle_return (st : ffi) (bytes : List word8)
  | Oracle_final (o : ffi_outcome)

export oracle_result (Oracle_return Oracle_final)

instance (ffi : Type) : Inhabited (oracle_result ffi) := ⟨.Oracle_final .FFI_failed⟩

/- HOL4:
Datatype:
  shmem_op = MappedRead | MappedWrite
End -/
inductive shmem_op
  | MappedRead | MappedWrite
  deriving DecidableEq, Inhabited

export shmem_op (MappedRead MappedWrite)

/- HOL4:
Datatype:
  ffiname = ExtCall mlstring | SharedMem shmem_op
End -/
inductive ffiname
  | ExtCall (s : mlstring)
  | SharedMem (o : shmem_op)
  deriving DecidableEq, Inhabited

export ffiname (ExtCall SharedMem)

/- HOL4:
Type oracle_function = “:'ffi -> word8 list -> word8 list -> 'ffi oracle_result”
Type oracle = “:ffiname -> 'ffi oracle_function” -/
abbrev oracle_function (ffi : Type) : Type := ffi → List word8 → List word8 → oracle_result ffi
abbrev oracle (ffi : Type) : Type := ffiname → oracle_function ffi

/- HOL4:
Datatype:
  io_event = IO_event ffiname (word8 list) ((word8 # word8) list)
End -/
inductive io_event
  | IO_event (s : ffiname) (conf : List word8) (bytes2 : List (word8 × word8))
  deriving DecidableEq, Inhabited

export io_event (IO_event)

/- HOL4:
Datatype:
  final_event = Final_event ffiname (word8 list) (word8 list) ffi_outcome
End -/
inductive final_event
  | Final_event (s : ffiname) (conf : List word8) (bytes : List word8) (o : ffi_outcome)
  deriving DecidableEq, Inhabited

export final_event (Final_event)

/- HOL4:
Datatype:
  ffi_state =
  <| oracle      : 'ffi oracle
   ; ffi_state   : 'ffi
   ; io_events   : io_event list
   |>
End -/
structure ffi_state (ffi : Type) where
  oracle : CmlTS.oracle ffi
  ffi_state : ffi
  io_events : List io_event

instance (ffi : Type) [Inhabited ffi] : Inhabited (ffi_state ffi) := ⟨⟨default, default, default⟩⟩

/- HOL4:
Datatype:
  ffi_result = FFI_return ('ffi ffi_state) (word8 list)
             | FFI_final final_event
End -/
inductive ffi_result (ffi : Type)
  | FFI_return (st : ffi_state ffi) (bytes : List word8)
  | FFI_final (e : final_event)

export ffi_result (FFI_return FFI_final)

instance (ffi : Type) : Inhabited (ffi_result ffi) := ⟨.FFI_final default⟩

/- HOL4:
Definition call_FFI_def:
  call_FFI (st:'ffi ffi_state) s conf bytes =
    if s ≠ ExtCall «» then
      case st.oracle s st.ffi_state conf bytes of
        Oracle_return ffi' bytes' =>
          if LENGTH bytes' = LENGTH bytes then
            FFI_return
              (st with
               <|ffi_state := ffi';
                 io_events :=
                   st.io_events ++ [IO_event s conf (ZIP (bytes,bytes'))]|>)
              bytes'
          else FFI_final (Final_event s conf bytes FFI_failed)
      | Oracle_final outcome =>
        FFI_final (Final_event s conf bytes outcome)
    else FFI_return st bytes
End -/
def call_FFI {ffi : Type} (st : ffi_state ffi) (s : ffiname) (conf bytes : List word8) :
    ffi_result ffi :=
  if s ≠ .ExtCall (mls "") then
    match st.oracle s st.ffi_state conf bytes with
    | .Oracle_return ffi' bytes' =>
      if bytes'.length = bytes.length then
        .FFI_return
          { st with
            ffi_state := ffi'
            io_events := st.io_events ++ [.IO_event s conf (List.zip bytes bytes')] }
          bytes'
      else .FFI_final (.Final_event s conf bytes .FFI_failed)
    | .Oracle_final outcome => .FFI_final (.Final_event s conf bytes outcome)
  else .FFI_return st bytes

/- HOL4:
Datatype:
  outcome = Success | Resource_limit_hit | FFI_outcome final_event
End -/
inductive outcome
  | Success | Resource_limit_hit | FFI_outcome (e : final_event)
  deriving DecidableEq, Inhabited

export outcome (Success Resource_limit_hit FFI_outcome)

/- HOL4:
Datatype:
  behaviour =
    Diverge (io_event llist)
  | Terminate outcome (io_event list)
  | Fail
End -/
inductive behaviour
  | Diverge (tr : llist io_event)
  | Terminate (o : outcome) (tr : List io_event)
  | Fail

export behaviour (Diverge Terminate Fail)

instance : Inhabited behaviour := ⟨.Fail⟩

end CmlTS
