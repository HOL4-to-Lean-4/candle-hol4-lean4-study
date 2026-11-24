import CandleLean.Prelude.PredSet

/-!
# HOL4 library: list, rich_list, indexedLists, sorting, mergesort

Lean core functions used directly (identical equations to HOL4):
`MAP` = `List.map`, `LENGTH` = `List.length`, `APPEND`/`++` = `++`, `FLAT` = `List.flatten`,
`REVERSE` = `List.reverse`, `FOLDR f e l` = `List.foldr f e l`, `FOLDL f e l` = `List.foldl f e l`,
`TAKE n l` = `List.take n l`, `DROP n l` = `List.drop n l`, `MEM x l` = `x ∈ l` (`List.Mem`),
`CONS`/`::`, `NIL`/`[]`.
The remaining HOL4 list constants are defined below with their HOL4 names.
-/

universe u v w

namespace HOL

open Classical

noncomputable section

/- HOL4: list$HD    Definition HD: HD (h::t) = h   (HD [] is unspecified) -/
private opaque HD_pkg {α : Type u} [Nonempty α] : {f : List α → α // ∀ h t, f (h :: t) = h} :=
  ⟨fun l => match l with | h :: _ => h | [] => Classical.choice inferInstance, fun _ _ => rfl⟩

def HD {α : Type u} [Nonempty α] : List α → α := HD_pkg.1

/-- The HOL4 defining theorem of `HD`. -/
theorem HD_def {α : Type u} [Nonempty α] (h : α) (t : List α) : HD (h :: t) = h := HD_pkg.2 h t

/- HOL4: list$TL    TL [] = [] /\ TL (h::t) = t -/
def TL {α : Type u} : List α → List α
  | [] => []
  | _ :: t => t

/- HOL4: list$EL    EL 0 l = (HD l:'a) /\ EL (SUC n) l = EL n (TL l) -/
def EL {α : Type u} [Nonempty α] : Nat → List α → α
  | 0, l => HD l
  | n + 1, l => EL n (TL l)

/- HOL4: list$NULL    (NULL [] = T) /\ (NULL (h::t) = F) -/
def NULL {α : Type u} : List α → Prop
  | [] => True
  | _ :: _ => False

/- HOL4: list$LAST    LAST (h::t) = if t = [] then h else LAST t   (LAST [] is unspecified) -/
private def LAST_wit {α : Type u} [Nonempty α] : List α → α
  | [] => Classical.choice inferInstance
  | h :: t => if t = [] then h else LAST_wit t

private opaque LAST_pkg {α : Type u} [Nonempty α] :
    {f : List α → α // ∀ h t, f (h :: t) = if t = [] then h else f t} :=
  ⟨LAST_wit, fun _ _ => by simp [LAST_wit]⟩

def LAST {α : Type u} [Nonempty α] : List α → α := LAST_pkg.1

/-- The HOL4 defining theorem of `LAST`. -/
theorem LAST_DEF {α : Type u} [Nonempty α] (h : α) (t : List α) :
    LAST (h :: t) = if t = [] then h else LAST t := LAST_pkg.2 h t

/- HOL4: list$FRONT    FRONT [] = [] /\ FRONT (h::t) = if t = [] then [] else h :: FRONT t -/
def FRONT {α : Type u} : List α → List α
  | [] => []
  | h :: t => if t = [] then [] else h :: FRONT t

/- HOL4: list$FILTER
     FILTER P [] = [] /\
     FILTER P (h::t) = if P h then (h::FILTER P t) else FILTER P t -/
def FILTER {α : Type u} (P : α → Prop) : List α → List α
  | [] => []
  | h :: t => if P h then h :: FILTER P t else FILTER P t

/- HOL4: list$EVERY    (EVERY P [] <=> T) /\ (EVERY P (h::t) <=> P h /\ EVERY P t) -/
def EVERY {α : Type u} (P : α → Prop) : List α → Prop
  | [] => True
  | h :: t => P h ∧ EVERY P t

/-- Well-founded-recursion preprocessing for `EVERY` (like Lean's `List.map_wfParam`), so that
definitions such as `type_ok` can be written literally as `EVERY (type_ok tysig) args`. -/
@[wf_preprocess] theorem Aux.EVERY_wfParam {α : Type u} {xs : List α} {P : α → Prop} :
    EVERY P (wfParam xs) = EVERY P xs.attach.unattach := by
  simp [wfParam]

@[wf_preprocess] theorem Aux.EVERY_unattach {α : Type u} {Q : α → Prop} {xs : List (Subtype Q)}
    {P : α → Prop} :
    EVERY P xs.unattach = EVERY (fun ⟨x, h⟩ =>
      binderNameHint x P <| binderNameHint h () <| P (wfParam x)) xs := by
  induction xs with
  | nil => simp [EVERY]
  | cons a t ih => simp [EVERY, ih, wfParam, binderNameHint]

/- HOL4: list$EXISTS    (EXISTS P [] <=> F) /\ (EXISTS P (h::t) <=> P h \/ EXISTS P t) -/
def EXISTS {α : Type u} (P : α → Prop) : List α → Prop
  | [] => False
  | h :: t => P h ∨ EXISTS P t

/- HOL4: list$LIST_TO_SET (overloaded as `set`)
     (!x. LIST_TO_SET [] x <=> F) /\
     (!h t x. LIST_TO_SET (h::t) x <=> (x = h) \/ LIST_TO_SET t x)
   (HOL4 `MEM h l` is the overload `h IN LIST_TO_SET l`; in Lean we write `h ∈ l`.) -/
def LIST_TO_SET {α : Type u} : List α → Set α
  | [] => fun _ => False
  | h :: t => fun x => x = h ∨ LIST_TO_SET t x

/- HOL4: list$ALL_DISTINCT
     (ALL_DISTINCT [] <=> T) /\ (ALL_DISTINCT (h::t) <=> ~MEM h t /\ ALL_DISTINCT t) -/
def ALL_DISTINCT {α : Type u} : List α → Prop
  | [] => True
  | h :: t => ¬ h ∈ t ∧ ALL_DISTINCT t

/- HOL4: list$SNOC    (SNOC x [] = [x]) /\ (SNOC x (CONS x' l) = CONS x' (SNOC x l)) -/
def SNOC {α : Type u} (x : α) : List α → List α
  | [] => [x]
  | x' :: l => x' :: SNOC x l

/- HOL4: list$GENLIST    GENLIST (f:num->'a) 0 = [] /\ GENLIST f (SUC n) = SNOC (f n) (GENLIST f n) -/
def GENLIST {α : Type u} (f : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => SNOC (f n) (GENLIST f n)

/- HOL4: list$REV    (REV [] acc = acc) /\ (REV (h::t) acc = REV t (h::acc)) -/
def REV {α : Type u} : List α → List α → List α
  | [], acc => acc
  | h :: t, acc => REV t (h :: acc)

/- HOL4: list$ZIP (uncurried; new_specification)
     (!l2. ZIP ([], l2) = []) /\ (!l1. ZIP (l1, []) = []) /\
     (!x1 l1 x2 l2. ZIP ((CONS x1 l1), (CONS x2 l2)) = CONS (x1,x2)(ZIP (l1, l2)))
   These equations determine ZIP on all inputs; it is Lean's `List.zip` on the pair. -/
def ZIP {α : Type u} {β : Type v} : List α × List β → List (α × β)
  | ([], _) => []
  | (_ :: _, []) => []
  | (x1 :: l1, x2 :: l2) => (x1, x2) :: ZIP (l1, l2)

/- HOL4: list$SUM    SUM [] = 0 /\ SUM (h::t) = h + SUM t -/
def SUM : List Nat → Nat
  | [] => 0
  | h :: t => h + SUM t

/- HOL4: list$PAD_LEFT    PAD_LEFT c n s = (GENLIST (K c) (n - LENGTH s)) ++ s -/
def PAD_LEFT {α : Type u} (c : α) (n : Nat) (s : List α) : List α :=
  GENLIST (K c) (n - s.length) ++ s

/- HOL4: list$PAD_RIGHT    PAD_RIGHT c n s = s ++ (GENLIST (K c) (n - LENGTH s)) -/
def PAD_RIGHT {α : Type u} (c : α) (n : Nat) (s : List α) : List α :=
  s ++ GENLIST (K c) (n - s.length)

/- HOL4: list$LIST_REL (overloaded as EVERY2)
     (LIST_REL R []      []      <=> T) /\
     (LIST_REL R (a::as) []      <=> F) /\
     (LIST_REL R []      (b::bs) <=> F) /\
     (LIST_REL R (a::as) (b::bs) <=> R a b /\ LIST_REL R as bs) -/
def LIST_REL {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | a :: as, b :: bs => R a b ∧ LIST_REL R as bs

/- HOL4: list$EVERY2 (overload)    EVERY2 = LIST_REL -/
@[reducible] def EVERY2 {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop :=
  LIST_REL R

/- HOL4: list$LLEX
     (LLEX R [] l2 <=> l2 <> []) /\
     (LLEX R (h1::t1) l2 <=>
        case l2 of
            [] => F
          | h2::t2 => if R h1 h2 then T
                      else if h1 = h2 then LLEX R t1 t2
                      else F) -/
def LLEX {α : Type u} (R : α → α → Prop) : List α → List α → Prop
  | [], l2 => l2 ≠ []
  | h1 :: t1, l2 =>
    match l2 with
    | [] => False
    | h2 :: t2 => if R h1 h2 then True else if h1 = h2 then LLEX R t1 t2 else False

/- HOL4: list$isPREFIX (overloaded as <<= and ≼)
     (isPREFIX [] l = T) /\
     (isPREFIX (h::t) l = case l of [] => F | h'::t' => (h = h') /\ isPREFIX t t') -/
def isPREFIX {α : Type u} : List α → List α → Prop
  | [], _ => True
  | h :: t, l =>
    match l with
    | [] => False
    | h' :: t' => h = h' ∧ isPREFIX t t'

/- HOL4: list$OPT_MMAP
     (OPT_MMAP f [] = SOME []) /\
     (OPT_MMAP f (h0::t0) =
        OPTION_BIND (f h0) (\h. OPTION_BIND (OPT_MMAP f t0) (\t. SOME (h::t)))) -/
def OPT_MMAP {α : Type u} {β : Type v} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | h0 :: t0 => Option.bind (f h0) (fun h => Option.bind (OPT_MMAP f t0) (fun t => some (h :: t)))

/- HOL4: indexedLists$MAPi
     (MAPi f [] = []) /\ (MAPi f (h::t) = f 0 h :: MAPi (f o SUC) t) -/
def MAPi {α : Type u} {β : Type v} : (Nat → α → β) → List α → List β
  | _, [] => []
  | f, h :: t => f 0 h :: MAPi (f ∘ Nat.succ) t

/- HOL4: rich_list$SPLITP
     (SPLITP P [] = ([],[])) /\
     (SPLITP P (CONS x l) =
        if P x then ([], CONS x l)
        else (CONS x (FST (SPLITP P l)), SND (SPLITP P l))) -/
def SPLITP {α : Type u} (P : α → Prop) : List α → List α × List α
  | [] => ([], [])
  | x :: l => if P x then ([], x :: l) else (x :: (SPLITP P l).1, (SPLITP P l).2)

theorem Aux.SPLITP_snd_length {α : Type u} (P : α → Prop) :
    ∀ l : List α, (SPLITP P l).2.length ≤ l.length
  | [] => by simp [SPLITP]
  | x :: l => by
    unfold SPLITP
    by_cases h : P x
    · simp [h]
    · simp only [h, if_false]
      have := Aux.SPLITP_snd_length P l
      simp only [List.length_cons]; omega

/- HOL4: rich_list$SEG (new_specification)
     ?SEG. (!k (l:'a list). SEG 0 k l = []) /\
           (!m x l. SEG (SUC m) 0 (CONS x l) = CONS x (SEG m 0 l)) /\
           (!m k x l. SEG (SUC m) (SUC k) (CONS x l) = SEG (SUC m) k l)
   (`SEG (SUC m) k []` is unspecified, as in HOL4). -/
def SEG_spec {α : Type u} (SEG : Nat → Nat → List α → List α) : Prop :=
  (∀ k l, SEG 0 k l = []) ∧
  (∀ m x l, SEG (m + 1) 0 (x :: l) = x :: SEG m 0 l) ∧
  (∀ m k x l, SEG (m + 1) (k + 1) (x :: l) = SEG (m + 1) k l)

private theorem SEG_exists {α : Type u} : ∃ f, SEG_spec (α := α) f := by
  refine ⟨fun m k l => List.take m (List.drop k l), ?_, ?_, ?_⟩
  · intro k l; simp
  · intro m x l; simp
  · intro m k x l; simp

private opaque SEG_pkg {α : Type u} : {f : Nat → Nat → List α → List α // SEG_spec f} :=
  ⟨Classical.choose SEG_exists, Classical.choose_spec SEG_exists⟩

def SEG {α : Type u} : Nat → Nat → List α → List α := SEG_pkg.1

/-- The HOL4 defining theorem of `SEG` (HOL4 `SEG`, from `new_specification`). -/
theorem SEG_def {α : Type u} : SEG_spec (SEG (α := α)) := SEG_pkg.2

/- HOL4: rich_list$MAX_LIST    (MAX_LIST [] = 0) /\ (MAX_LIST (h::t) = MAX h (MAX_LIST t)) -/
def MAX_LIST : List Nat → Nat
  | [] => 0
  | h :: t => MAX h (MAX_LIST t)

/-! ## sorting -/

/- HOL4: sorting$PERM    PERM L1 L2 = !x. FILTER ($= x) L1 = FILTER ($= x) L2 -/
def PERM {α : Type u} (L1 L2 : List α) : Prop :=
  ∀ x, FILTER (fun y => x = y) L1 = FILTER (fun y => x = y) L2

/- HOL4: sorting$SORTED
     (SORTED R [] = T) /\ (SORTED R [x] = T) /\
     (SORTED R (x::y::rst) <=> R x y /\ SORTED R (y::rst)) -/
def SORTED {α : Type u} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rst => R x y ∧ SORTED R (y :: rst)

/-! ## mergesort (tail-recursive versions used by `mllist$sort`) -/

/- HOL4: mergesort$sort2_tail
     sort2_tail (neg:bool) R x y = if R x y <> neg then [x;y] else [y;x] -/
def sort2_tail {α : Type u} (neg : Prop) (R : α → α → Prop) (x y : α) : List α :=
  if R x y ≠ neg then [x, y] else [y, x]

/- HOL4: mergesort$sort3_tail
     sort3_tail (neg:bool) R x y z =
      if R x y <> neg then
        if R y z <> neg then [x;y;z]
        else if R x z <> neg then [x;z;y]
        else [z;x;y]
      else if R y z <> neg then
        if R x z <> neg then [y;x;z]
        else [y;z;x]
      else [z;y;x] -/
def sort3_tail {α : Type u} (neg : Prop) (R : α → α → Prop) (x y z : α) : List α :=
  if R x y ≠ neg then
    if R y z ≠ neg then [x, y, z]
    else if R x z ≠ neg then [x, z, y]
    else [z, x, y]
  else if R y z ≠ neg then
    if R x z ≠ neg then [y, x, z]
    else [y, z, x]
  else [z, y, x]

/- HOL4: mergesort$merge_tail
     (merge_tail (negate:bool) R [] [] acc = acc) /\
     (merge_tail negate R l [] acc = REV l acc) /\
     (merge_tail negate R [] l acc = REV l acc) /\
     (merge_tail negate R (x::l1) (y::l2) acc =
       if R x y <> negate then
         merge_tail negate R l1 (y::l2) (x::acc)
       else
         merge_tail negate R (x::l1) l2 (y::acc)) -/
def merge_tail {α : Type u} (negate : Prop) (R : α → α → Prop) :
    List α → List α → List α → List α
  | [], [], acc => acc
  | l, [], acc => REV l acc
  | [], l, acc => REV l acc
  | x :: l1, y :: l2, acc =>
    if R x y ≠ negate then merge_tail negate R l1 (y :: l2) (x :: acc)
    else merge_tail negate R (x :: l1) l2 (y :: acc)
termination_by l1 l2 => l1.length + l2.length

/- HOL4: mergesort$mergesortN_tail
     (mergesortN_tail (negate :bool) R 0 l = []) /\
     (mergesortN_tail negate R 1 (x::l) = [x]) /\
     (mergesortN_tail negate R 1 [] = []) /\
     (mergesortN_tail negate R 2 (x::y::l) = sort2_tail negate R x y) /\
     (mergesortN_tail negate R 2 [x] = [x]) /\
     (mergesortN_tail negate R 2 [] = []) /\
     (mergesortN_tail negate R 3 (x::y::z::l) = sort3_tail negate R x y z) /\
     (mergesortN_tail negate R 3 [x;y] = sort2_tail negate R x y) /\
     (mergesortN_tail negate R 3 [x] = [x]) /\
     (mergesortN_tail negate R 3 [] = []) /\
     (mergesortN_tail negate R n l =
       let len1 = DIV2 n in
       let neg = ~negate in
         merge_tail neg R (mergesortN_tail neg R (DIV2 n) l)
                          (mergesortN_tail neg R (n - len1) (DROP len1 l))
                          [])
   The last (catch-all) clause only applies when n >= 4 (all smaller n are covered by the
   earlier clauses), so it is written with the pattern `n + 4`. -/
def mergesortN_tail {α : Type u} (negate : Prop) (R : α → α → Prop) : Nat → List α → List α
  | 0, _ => []
  | 1, x :: _ => [x]
  | 1, [] => []
  | 2, x :: y :: _ => sort2_tail negate R x y
  | 2, [x] => [x]
  | 2, [] => []
  | 3, x :: y :: z :: _ => sort3_tail negate R x y z
  | 3, [x, y] => sort2_tail negate R x y
  | 3, [x] => [x]
  | 3, [] => []
  | n + 4, l =>
    let len1 := DIV2 (n + 4)
    let neg := ¬ negate
    merge_tail neg R (mergesortN_tail neg R (DIV2 (n + 4)) l)
                     (mergesortN_tail neg R ((n + 4) - len1) (List.drop len1 l))
                     []
termination_by n _ => n
decreasing_by all_goals (simp only [DIV2]; omega)

/- HOL4: mergesort$mergesort_tail    mergesort_tail R l = mergesortN_tail F R (LENGTH l) l -/
def mergesort_tail {α : Type u} (R : α → α → Prop) (l : List α) : List α :=
  mergesortN_tail False R l.length l

end

end HOL
