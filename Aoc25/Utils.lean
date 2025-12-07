import Init.Data.Array.Lemmas
import Init.Data.Vector.Basic
import Std.Internal.Parsec.String
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Basic

--notation "Array₂ " α => Array (Array α)
abbrev Array₂ (α : Type _) := Array (Array α)
abbrev Vector₂ (α : Type _) (n m : Nat) := Vector (Vector α m) n

section general

def checkThatProp (p : Prop) [Decidable p] : Option (PLift p) :=
  if h : p then some ⟨h⟩ else none

def checkThat {α : Type _} (x : α) (p : α → Prop) [∀ a, Decidable (p a)] :
    Option (PLift (p x)) :=
  if h : p x then some ⟨h⟩
  else none

def Array.checkThatAll {α : Type _} (xs : Array α) (p : α → Prop) [∀ a, Decidable (p a)] :
    Option (PLift (∀ i, (h : i < xs.size) → p xs[i])) :=
  match h : xs.all p with
  | false => none
  | true =>
      have hmain : ∀ (i : Fin xs.size), p xs[i] := by
        have htmp := (xs.all_eq_true).mp h
        simp only [decide_eq_true_eq] at htmp
        exact fun i =>
          htmp (↑i) (Fin.val_lt_of_le i (of_eq_true (by simp)))
      some ⟨fun i hi => hmain ⟨i, hi⟩⟩

def Array.checkThatUpTo {α : Type _} (xs : Array α) (n : Nat) (hn : n ≤ xs.size) (p : α → Prop)
    [∀ a, Decidable (p a)] :
    Option (PLift (∀ i, (h : i < n) → p (xs[i]'(Nat.lt_of_lt_of_le h hn)))) :=
  if hzero : xs.size = 0 then
    have hmain : ∀ i, (h : i < n) → p (xs[i]'(Nat.lt_of_lt_of_le h hn)) := by
      intro i hi
      have : i < 0 := by
        calc i < n := hi
             _ ≤ xs.size := hn
             _ = 0 := hzero
      exact False.elim <| Nat.not_lt_zero i this
    some ⟨hmain⟩
  else
    match h : xs.all p (start := 0) (stop := n) with
    | false => none
    | true =>
        have hmain := by
          have htmp := (xs.all_iff_forall).mp h
          simpa [decide_eq_true_iff] using htmp
        have hmain' (i : Nat) (hi : i < n) : p (xs[i]'(Nat.lt_of_lt_of_le hi hn)) := by
          exact hmain i (Nat.lt_of_lt_of_le hi hn) hi
        some ⟨hmain'⟩

def Array.toVectorFixed (xs : Array α) (n : Nat) : Option (Vector α n) := do
  let ⟨h⟩ ← checkThat xs (fun z => z.size = n)
  return ⟨xs, h⟩

def noop [Monad m] : m Unit := do
  return ⟨⟩

end general

/- ## Char -/
namespace Char

def toNatDigit (c : Char) : Nat :=
  c.toNat - 48

def toNatDigit? (c : Char) : Option Nat :=
  if c.isDigit then some c.toNatDigit else none

end Char

/- ## String -/
namespace String

def ofCharList (l : List Char) : String :=
  match l with
  | [] => ""
  | [c] => c.toString
  | c :: tail => c.toString ++ ofCharList tail

def toCharArray (s : String) : Array Char := s.toList.toArray

def ofCharArray (a : Array Char) : String := .ofCharList a.toList

end String

/- ## Parser -/
namespace Std.Internal.Parsec.String

def _root_.String.yoloParse [Inhabited α] (str : String) (p : Parser α) : α :=
  match Parser.run p str with
  | .ok res => res
  | .error _ => panic! "Parse error!"

def _root_.String.parse? (str : String) (p : Parser α) : Option α :=
  match Parser.run p str with
  | .ok res => some res
  | .error _ => none

def digitsFin (n : Nat) : Parser (Fin n) := do
  let x ← digits
  let some ⟨h⟩ := checkThat x (fun z => z < n) | fail s!"Expected a number < {n}"
  return ⟨x, h⟩

@[inline, specialize]
partial def foldlP (f : β → α → Parser β) (init : β) (p : Parser α) : Parser β :=
  tryCatch p
    (fun a => do foldlP f (← f init a) p)
    (fun _ => return init)

@[inline, specialize]
def takeVec (n : Nat) (p : Parser α) : Parser (Vector α n) := do
  let mut acc := #[]
  for _ in 0...n do
    let nxt ← p
    acc := acc.push nxt
  let some ⟨h⟩ := checkThat acc.size (fun x => x = n) | fail s!"Expected {n} elements"
  return ⟨acc, h⟩

@[inline, specialize]
def sepBy (sep : Parser β) (p : Parser α) (strict : Bool := false) :
    Parser (Array α) := do
  let f (acc : Array α) (a : α) : Parser (Array α) := return acc.push a
  let p' : Parser α := do
    let nxt ← p
    if strict then
      let _ ← sep
      return nxt
    else
      tryCatch sep (fun _ => return nxt) (fun _ => return nxt)
  foldlP f #[] p'

@[inline]
def sepByVec (n : Nat) (sep : Parser β) (p : Parser α) (strict : Bool := false) :
    Parser (Vector α n) := do
  let mut acc := #[]
  if hn : n = 0 then return ⟨#[], by grind⟩
  for _ in 0...n-1 do
    let nxt ← p
    let _ ← sep
    acc := acc.push nxt
  let nxt ← p
  if strict then let _ ← sep else tryCatch sep (fun _ => return ⟨⟩) (fun _ => return ⟨⟩)
  acc := acc.push nxt
  let some ⟨h⟩ := checkThat acc.size (fun x => x = n) | fail s!"Expected {n} elements"
  return ⟨acc, h⟩

def oneOf (cs : Array Char) : Parser Char := do
  let c ← any
  if cs.contains c then return c else failure

end Std.Internal.Parsec.String

namespace Array

/-- Search for an element in an array that is sorted by the value of `f`. -/
partial def binSearchMap [Inhabited α] [Ord β] (as : Array α) (k : β) (f : α → β) (lo : Nat := 0)
    (hi : Nat := as.size - 1) : Option α :=
  if lo ≤ hi then
    let _ : LT β := ltOfOrd
    let m := (lo + hi)/2
    let a := as[m]!
    if f a < k then binSearchMap as k f (m+1) hi
    else if k < f a then
      if m == 0 then none
      else binSearchMap as k f lo (m-1)
    else some a
  else none

/-- Search for the first element that satisfies `p : α → Bool` (assumed to be monotone) in an array
that is sorted by the value of `f`. Returns the position if one such element is found. -/
partial def binSearchMapSat [Inhabited α] [Ord β] (as : Array α) (p : α → Bool) (f : α → β)
    (lo : Nat := 0) (hi : Nat := as.size - 1) : Option Nat :=
  if lo = hi then
    if p as[lo]! then some lo else none
  else if lo < hi then
    let _ : LT β := ltOfOrd
    let m := (lo + hi)/2
    let a := as[m]!
    if p a then binSearchMapSat as p f lo m
    else binSearchMapSat as p f (m+1) hi
  else none

def findIdx! (as : Array α) (p : α → Bool) : Nat :=
  match as.findIdx? p with
  | some x => x
  | none => panic!"Element not found"

def filterWithIdx (as : Array α) (p : Nat → α → Bool) : Array α :=
  (·.2) <| as.foldl (init := (0, Array.empty)) fun (idx, r) a =>
    if p idx a then
      (idx+1, r.push a)
    else
      (idx+1, r)

def foldlIdx (as : Array α) (f : Nat → β → α → β) (init : β) : β :=
  (as.foldl (β := β × Nat) (init := ⟨init, 0⟩) fun acc elem => ⟨f acc.2 acc.1 elem, acc.2 + 1⟩).1

def mkArray₂ (m n : Nat) (v : α) : Array (Array α) :=
  .replicate m (.replicate n v)

def foldtlM [Monad m] (f : β → α → m β) (init : β) (a : Array (Array α)) : m β :=
  a.foldlM (fun x row => row.foldlM f x) init

def foldtl (f : β → α → β) (init : β) (a : Array (Array α)) : β :=
  a.foldl (fun x row => row.foldl f x) init

def transpose [Inhabited α] (as : Array₂ α) : Option (Array₂ α) := do
  let dim := as.size
  if hdim : dim ≤ 0 then
    return #[]
  else
    have _ := Nat.lt_of_not_ge hdim
    let width := as[0].size
    let some ⟨_⟩ := as.checkThatAll fun row => row.size = width | failure
    let mut output : Array₂ α := #[]
    for i in [0:width] do
      let curCol := as.map (fun row => row[i]!)
      output := output.push curCol
    return output

def zipWith2D (f : α → β → γ) (a : Array (Array α)) (b : Array (Array β)) : Array (Array γ) :=
  a.zipWith (fun ra rb => ra.zipWith f rb) b

def modify₂ (a : Array (Array α)) (i j : Nat) (f : α → α) : Array (Array α) :=
  a.modify i (·.modify j f)

def get₂! [Inhabited α] (a : Array₂ α) (i j : Nat) : α := a[i]![j]!

def set₂ (a : Array (Array α)) (i j : Nat) (x : α) : Array (Array α) :=
  a.modify i (·.modify j (fun _ => x))

def containsAny (as : Array α) (p : α → Bool) : Bool := Id.run do
  for a in as do
    if p a then return true
  return false

def last? (as : Array α) : Option α := as[as.size-1]?

def last (as : Array α) (h : 0 < as.size) : α := as[as.size-1]

def maybePush (as : Array α) (a? : Option α) : Array α :=
  match a? with
  | none => as
  | some x => as.push x

def best? (as : Array α) (keep : α → α → α) : Option α :=
  as.foldl (init := none) fun acc x => match acc with
                                       | none => some x
                                       | some z => some (keep z x)

def best! [Inhabited α] (as : Array α) (keep : α → α → α) : α :=
  match as.best? keep with
  | none => panic! "empty array (best!)"
  | some x => x

def bestD (as : Array α) (keep : α → α → α) (d : α) : α :=
  match as.best? keep with | none => d | some x => x

def getAllIdx (as : Array α) (p : α → Bool) : Array Nat :=
  as.foldlIdx (init := #[]) fun i ar elem => if p elem then ar.push i else ar

def foldlMSlidingWinIdx [Monad m] (as : Array α) (n : Nat) (init : β)
    (f : β → Array α → Nat → m β) : m β := do
  let out ← as.foldlM (init := (⟨init, ⟨#[], 0⟩⟩ : β × Array α × Nat)) fun (st : β × Array α × Nat) a => do
    let newwin : Array α := if st.2.1.size = n then (st.2.1.drop 1).push a else st.2.1.push a
    return ⟨← f st.1 newwin st.2.2, ⟨newwin, st.2.2 + 1⟩⟩
  return out.1

def foldlSlidingWinIdx (as : Array α) (n : Nat) (init : β)
    (f : β → Array α → Nat → β) : β :=
  as.foldlMSlidingWinIdx (m := Id) n init f

def toVector'' (as : Array α) : Σ n : Nat, (Vector α n) := ⟨as.size, ⟨as, rfl⟩⟩

def toVector' (as : Array α) (n : Nat) : Option (Vector α n) :=
  match checkThat as (fun bs => bs.size = n) with
  | none => none
  | some ⟨hmain⟩ => some ⟨as, hmain⟩

def toVector₂ (as : Array₂ α) : Option (Σ (n m : Nat), Vector₂ α n m) := do
  if h : 0 < as.size then
    let m := as[0].size
    let n := as.size
    let as' ← as.mapM (m := Option) fun a => do
      let out ← a.toVector' m
      return out
    let out ← as'.toVector' n
    return ⟨n, m, out⟩
  else
    return ⟨0, 0, #v[]⟩

def toVector₂' (as : Array₂ α) (n m : Nat) : Option (Vector₂ α n m) := do
  let as' ← as.mapM fun a => return ← a.toVector' m
  return ← as'.toVector' n

def pad (as : Array α) (n : Nat) (a : α) : Vector α n :=
  as.foldlIdx (init := .replicate n a) fun i acc cur => acc.setIfInBounds i cur

end Array

/- ## Vector -/
namespace Vector

def getIntD (v : Vector α n) (i : Int) (d : α) : α :=
  match i.toNat? with
  | none => d
  | some i' => if h : i' < n then v[i'] else d

def modify (v : Vector α n) (i : Nat) (f : α → α) : Vector α n := ⟨v.1.modify i f, by simp⟩

end Vector

/- ## Array₂ -/
namespace Array₂

def printBoolGrid (grid : Array₂ Bool) : IO Unit := do
  for ln in grid do
    let charline := ln.map fun b => if b then '#' else '·'
    let str := String.ofCharArray charline
    IO.println str

def printCharGrid (grid : Array₂ Char) : IO Unit := do
  for ln in grid do
    let str := String.ofCharArray ln
    IO.println str

end Array₂

/- ## Vector₂ -/
namespace Vector₂

def set (v : Vector₂ α n m) (i j : Nat) (x : α) (hi : i < n := by get_elem_tactic)
    (hj : j < m := by get_elem_tactic) : Vector₂ α n m :=
  Vector.set v i (v[i].set j x)

def setIfInBounds (v : Vector₂ α n m) (i j : Int) (x : α) : Vector₂ α n m := Id.run do
  let some i' := i.toNat? | return v
  let some j' := j.toNat? | return v
  if hi : i' < n then
    if hj : j' < m then
      return v.set i' j' x
  return v

def set! [Inhabited α] (v : Vector₂ α n m) (i j : Nat) (x : α) : Vector₂ α n m :=
  Vector.set! v i (v[i]!.set! j x)

def get₂? (v : Vector₂ α n m) (i j : Int) : Option α := do
  let i' ← i.toNat?
  let j' ← j.toNat?
  let w ← v[i']?
  return ← w[j']?

def map (v : Vector₂ α n m) (f : α → β) : Vector₂ β n m :=
  Vector.map (fun w => w.map f) v

def zipWith (f : α → β → γ) (a : Vector₂ α n m) (b : Vector₂ β n m) : Vector₂ γ n m :=
  Vector.zipWith (fun v w => Vector.zipWith f v w) a b

def mkVector₂ (n m : Nat) (v : α) : Vector₂ α n m :=
  Vector.replicate n (Vector.replicate m v)

def toArray₂ (a : Vector₂ α n m) : Array₂ α :=
  a.toArray.map Vector.toArray

def printBoolGrid (grid : Vector₂ Bool n m) : IO Unit :=
  grid.toArray₂.printBoolGrid

def printCharGrid (grid : Vector₂ Char n m) : IO Unit :=
  grid.toArray₂.printCharGrid

def findElem [BEq α] (grid : Vector₂ α n m) (a : α) : Option (Nat × Nat) := do
  for hy : y in [:n] do
    for hx : x in [:m] do
      if grid[y][x] == a then return ⟨y, x⟩
  failure

/-- Here `p` is supposed to parse a whole line. -/
def getGrid (input : Array String) (p : Std.Internal.Parsec.String.Parser (Array α)) :
    Option (Σ (n m : Nat), Vector₂ α n m) := do
  let lines ← input.mapM <| fun s => s.parse? p
  return (← lines.toVector₂)

end Vector₂

namespace List

def orderedInsert (lst : List α) (a : α) (le : α → α → Bool) : List α :=
  match lst with
  | [] => [a]
  | b :: l => if le a b then a :: b :: l else b :: l.orderedInsert a le

end List

namespace Std.HashMap

variable [BEq α] [Hashable α]

def push (m : Std.HashMap α (Array β)) (a : α) (b : β) : Std.HashMap α (Array β) :=
  m.alter a fun bs =>
    match bs with
    | none => #[b]
    | some bs' => bs'.push b

def findSuchThat [BEq α] [Hashable α] (m : Std.HashMap α β) (p : α → β → Bool) : Option α :=
  m.fold (init := none) fun _ a b => if p a b then some a else none

def print [BEq α] [LawfulBEq α] [Hashable α] [ToString α] [ToString β]
    (data : Std.HashMap α β) : IO Unit := do
  for hk : k in data.keys do
    IO.println s!"{k} => {data[k]'(by grind)}"

@[inline]
def insertOrModify [BEq α] [Hashable α] (m : Std.HashMap α β) (k : α) (f : β → β) (init : β) : Std.HashMap α β :=
  if m.contains k then m.modify k f else m.insert k init

theorem size_le_fin (m : Std.HashMap (Fin n) β) : m.size ≤ n := by
  suffices ∀ k : Nat, k ≤ n → (∀ x ∈ m, x < k) → m.size ≤ k from this n (Nat.le_refl _) (fun x _ => x.2)
  intro k
  induction k generalizing m with
  | zero => simp [← Std.HashMap.isEmpty_iff_forall_not_mem, Std.HashMap.isEmpty_eq_size_eq_zero]
  | succ k ih =>
    intro hm hl'
    have := ih (m.erase ⟨k, by omega⟩) (by omega) (by
      simp only [HashMap.mem_erase, beq_eq_false_iff_ne, ne_eq, and_imp]
      intro ⟨x, hx⟩ hx' hx''
      have := hl' _ hx''
      simp_all; omega)
    have := HashMap.size_le_size_erase (m := m) (k := ⟨k, by omega⟩)
    omega

end Std.HashMap

namespace Std.HashSet

def containsSuchThat [BEq α] [Hashable α] (m : Std.HashSet α) (p : α → Bool) : Bool :=
  m.fold (init := false) fun _ a => if p a then true else false

end Std.HashSet

/- Stuff about the state monad. -/
namespace StateM

def runState (x : StateM σ α) (s : σ) : σ := (x.run s).2

end StateM

section misc

def IO.exitWithError (e : String) : IO α := do
  IO.println e
  IO.Process.exit 0

def Array.toCharGrid (lines : Array String) : Option (Σ (n m : Nat), Vector₂ Char n m) :=
  (lines.map (·.toCharArray)).toVector₂

def Nat.log10 (n : Nat) (out : Nat := 0) : Nat :=
  match n with
  | 0 => out
  | k+1 => 1 + log10 ((k+1) / 10)

def Nat.toNatDigits (n : Nat) : Array Nat :=
  let rec go (m : Nat) (ds : Array Nat) :=
    if m = 0 then ds else go (m / 10) (ds.push (m % 10))
  (go n #[]).reverse

def IO.getln : IO String := do (← getStdin).getLine

end misc
