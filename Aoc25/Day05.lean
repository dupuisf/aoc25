import Aoc25.Utils

open System Std.Internal.Parsec.String

namespace Day05

def testinput1 : FilePath := "input_05_test1"
def testinput2 : FilePath := "input_05_test2"
def realinput : FilePath := "input_05"

/-
PART 1:
-/

def parseRange : Parser (Nat × Nat) := do
  let l ← digits
  let _ ← pchar '-'
  let d ← digits
  if d < l then failure
  return (l, d)

def isFresh (fresh : Array (Nat × Nat)) (id : Nat) : Bool := Id.run do
  for ⟨l, r⟩ in fresh do
    if l ≤ id ∧ id ≤ r then return true
  return false

def firstPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let some splitpoint := raw.findIdx? (· == "") | IO.exitWithError "Couldn't find second block"
  let some fresh := raw.take splitpoint |>.mapM fun s => s.parse? parseRange
    | IO.exitWithError "Invalid first block"
  let some available := raw.drop (splitpoint + 1) |>.mapM fun s => s.parse? digits
    | IO.exitWithError "Second block contains things other than numbers"
  let mut total := 0
  for id in available do
    if isFresh fresh id then total := total + 1
  return total

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let some splitpoint := raw.findIdx? (· == "") | IO.exitWithError "Couldn't find second block"
  let some fresh := raw.take splitpoint |>.mapM fun s => s.parse? parseRange
    | IO.exitWithError "Invalid first block"
  -- sort by increasing start of range
  let ⟨n, fsorted⟩ := (fresh.qsort (fun x y => x.1 < y.1)).toVector''
  let some ⟨hn⟩ := checkThat n (0 < ·) | IO.exitWithError "Empty array"
  let mut left := fsorted[0].1
  let mut right := fsorted[0].2
  let mut total := 0
  for hi : i in 1...<n do
    let l := fsorted[i].1
    let r := fsorted[i].2
    if l > right then
      total := total + right - left + 1
      left := l
      right := r
    else
      if r > right then right := r
  total := total + right - left + 1
  return total

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day05
