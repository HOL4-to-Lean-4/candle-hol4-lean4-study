import CmlTS.Prelude.Set
/-
  Translation of HOL4 theory `location` (locationScript.sml).
-/
set_option autoImplicit false

namespace CmlTS

/- HOL4:
Datatype: locn = UNKNOWNpt | EOFpt | POSN num num
End -/
inductive locn
  | UNKNOWNpt | EOFpt | POSN (r c : Nat)
  deriving DecidableEq, Inhabited

export locn (UNKNOWNpt EOFpt POSN)

/- HOL4:
Definition locnrow_def:
  locnrow (POSN r c) = r
End
val _ = add_record_field ("row", “locnrow”)
   (ARB on the other constructors) -/
noncomputable def locnrow : locn → Nat
  | .POSN r _ => r
  | _ => ARB

/- HOL4:
Definition locn_rowupdate_def:
  locn_rowupdate f (POSN r c) = POSN (f r) c
End
val _ = add_record_fupdate ("row", “locn_rowupdate”)
   (ARB on the other constructors) -/
noncomputable def locn_rowupdate (f : Nat → Nat) : locn → locn
  | .POSN r c => .POSN (f r) c
  | _ => ARB

/- HOL4:
Definition locncol_def:
  locncol (POSN r c) = c
End
val _ = add_record_field ("col", “locncol”)
   (ARB on the other constructors) -/
noncomputable def locncol : locn → Nat
  | .POSN _ c => c
  | _ => ARB

/- HOL4:
Definition locn_colupdate_def:
  locn_colupdate f (POSN r c) = POSN r (f c)
End
val _ = add_record_fupdate ("col", “locn_colupdate”)
   (ARB on the other constructors) -/
noncomputable def locn_colupdate (f : Nat → Nat) : locn → locn
  | .POSN r c => .POSN r (f c)
  | _ => ARB

/- HOL4:
Datatype: locs = Locs locn locn
End -/
inductive locs
  | Locs (l1 l2 : locn)
  deriving DecidableEq, Inhabited

export locs (Locs)

end CmlTS
