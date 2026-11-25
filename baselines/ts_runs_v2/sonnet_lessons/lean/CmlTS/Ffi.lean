import CmlTS.Misc
import CmlTS.Mlstring

/-!
# ffi (HOL4 theory `ffi`): definition of the FFI type
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   Datatype:
     ffi_outcome = FFI_failed | FFI_diverged
   End -/
inductive ffi_outcome : Type where
  | FFI_failed : ffi_outcome
  | FFI_diverged : ffi_outcome

instance : Inhabited ffi_outcome := ⟨.FFI_failed⟩

/- HOL4:
   Datatype:
     oracle_result = Oracle_return 'ffi (word8 list) | Oracle_final ffi_outcome
   End -/
inductive oracle_result (α : Type u) : Type u where
  | Oracle_return (s : α) (bs : List word8) : oracle_result α
  | Oracle_final (o : ffi_outcome) : oracle_result α

/- HOL4:
   Datatype:
     shmem_op = MappedRead | MappedWrite
   End -/
inductive shmem_op : Type where
  | MappedRead : shmem_op
  | MappedWrite : shmem_op

instance : Inhabited shmem_op := ⟨.MappedRead⟩

/- HOL4:
   Datatype:
     ffiname = ExtCall mlstring | SharedMem shmem_op
   End -/
inductive ffiname : Type where
  | ExtCall (s : mlstring) : ffiname
  | SharedMem (op : shmem_op) : ffiname

instance : Inhabited ffiname := ⟨.SharedMem default⟩

/- HOL4:
   Type oracle_function = “:'ffi -> word8 list -> word8 list -> 'ffi oracle_result”
   Type oracle = “:ffiname -> 'ffi oracle_function” -/
abbrev oracle_function (α : Type u) : Type u :=
  α → List word8 → List word8 → oracle_result α
abbrev oracle (α : Type u) : Type u := ffiname → oracle_function α

/- HOL4:
   (* An I/O event, IO_event s bytes bytes2, represents the call of FFI function s with
    * immutable input bytes and mutable input map fst bytes2,
    * returning map snd bytes2 in the mutable array. *)
   Datatype:
     io_event = IO_event ffiname (word8 list) ((word8 # word8) list)
   End -/
inductive io_event : Type where
  | IO_event (n : ffiname) (a : List word8) (b : List (word8 × word8)) : io_event

instance : Inhabited io_event := ⟨.IO_event default [] []⟩

/- HOL4:
   Datatype:
     final_event = Final_event ffiname (word8 list) (word8 list) ffi_outcome
   End -/
inductive final_event : Type where
  | Final_event (n : ffiname) (a b : List word8) (o : ffi_outcome) : final_event

instance : Inhabited final_event := ⟨.Final_event default [] [] default⟩

/- HOL4:
   Datatype:
     ffi_state =
     <| oracle      : 'ffi oracle
      ; ffi_state   : 'ffi
      ; io_events   : io_event list
      |>
   End -/
structure ffi_state (α : Type u) : Type u where
  oracle : oracle α
  ffi_state : α
  io_events : List io_event

/- HOL4:
   Datatype:
     ffi_result = FFI_return ('ffi ffi_state) (word8 list)
                | FFI_final final_event
   End -/
inductive ffi_result (α : Type u) : Type u where
  | FFI_return (st : ffi_state α) (bs : List word8) : ffi_result α
  | FFI_final (e : final_event) : ffi_result α

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
def call_FFI {α : Type u} (st : ffi_state α) (s : ffiname) (conf bytes : List word8) :
    ffi_result α :=
  if s ≠ .ExtCall (.strlit []) then
    match st.oracle s st.ffi_state conf bytes with
    | .Oracle_return ffi' bytes' =>
      if LENGTH bytes' = LENGTH bytes then
        .FFI_return
          { st with
            ffi_state := ffi',
            io_events := st.io_events ++ [.IO_event s conf (ZIP (bytes, bytes'))] }
          bytes'
      else .FFI_final (.Final_event s conf bytes .FFI_failed)
    | .Oracle_final outcome => .FFI_final (.Final_event s conf bytes outcome)
  else .FFI_return st bytes

/- HOL4:
   Datatype:
     outcome = Success | Resource_limit_hit | FFI_outcome final_event
   End -/
inductive outcome : Type where
  | Success : outcome
  | Resource_limit_hit : outcome
  | FFI_outcome (e : final_event) : outcome

/- HOL4:
   (* A program can Diverge, Terminate, or Fail. ... *)
   Datatype:
     behaviour =
       Diverge (io_event llist)
     | Terminate outcome (io_event list)
     | Fail
   End -/
inductive behaviour : Type where
  | Diverge (l : llist io_event) : behaviour
  | Terminate (o : outcome) (l : List io_event) : behaviour
  | Fail : behaviour

end
