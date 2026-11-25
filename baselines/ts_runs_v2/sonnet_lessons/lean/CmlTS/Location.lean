import CmlTS.Prelude.Basic
import CmlTS.Prelude.List
import CmlTS.Prelude.Num

/-!
# location (HOL4 theory `location`)
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   Datatype: locn = UNKNOWNpt | EOFpt | POSN num num
   End -/
inductive locn : Type where
  | UNKNOWNpt : locn
  | EOFpt : locn
  | POSN (r c : Nat) : locn

instance : Inhabited locn := ⟨.UNKNOWNpt⟩

/- HOL4:
   Definition locnrow_def:
     locnrow (POSN r c) = r
   End
   val _ = add_record_field ("row", “locnrow”)
   (other constructors: unspecified, `ARB`) -/
def locnrow : locn → Nat
  | .POSN r _ => r
  | _ => ARB

/- HOL4:
   Definition locn_rowupdate_def:
     locn_rowupdate f (POSN r c) = POSN (f r) c
   End
   val _ = add_record_fupdate ("row", “locn_rowupdate”)
   (other constructors: unspecified, `ARB`) -/
def locn_rowupdate (f : Nat → Nat) : locn → locn
  | .POSN r c => .POSN (f r) c
  | _ => ARB

/- HOL4:
   Definition locncol_def:
     locncol (POSN r c) = c
   End
   val _ = add_record_field ("col", “locncol”)
   (other constructors: unspecified, `ARB`) -/
def locncol : locn → Nat
  | .POSN _ c => c
  | _ => ARB

/- HOL4:
   Definition locn_colupdate_def:
     locn_colupdate f (POSN r c) = POSN r (f c)
   End
   val _ = add_record_fupdate ("col", “locn_colupdate”)
   (other constructors: unspecified, `ARB`) -/
def locn_colupdate (f : Nat → Nat) : locn → locn
  | .POSN r c => .POSN r (f c)
  | _ => ARB

/- HOL4:
   Datatype: locs = Locs locn locn
   End -/
inductive locs : Type where
  | Locs (l1 l2 : locn) : locs

instance : Inhabited locs := ⟨.Locs default default⟩

end
