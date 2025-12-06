import Aoc25.Utils

open System Std.Internal.Parsec.String Std.Internal.Parsec

namespace Day06

def testinput1 : FilePath := "input_06_test1"
def testinput2 : FilePath := "input_06_test2"
def realinput : FilePath := "input_06"

/-
PART 1:
-/

inductive Op where
| mul
| add
deriving DecidableEq, Repr

instance : ToString Op where
  toString op := match op with
                 | .add => "+"
                 | .mul => "*"

def parseOp : Parser Op := do
  let c ← any
  if c == '*' then
    return .mul
  if c == '+' then
    return .add
  failure

def getLines (r : Array String) : Option (Array₂ Nat) := do
  let mut lines : Array₂ Nat := #[]
  for hi : i in 0...<r.size - 1 do
    let some l := r[i].parse? (sepBy ws digits) | failure
    lines := lines.push l
  return lines

def solveProb (nums : Array Nat) (op : Op) : Nat :=
  match op with
  | .add => nums.sum
  | .mul => nums.foldl (init := 1) (· * ·)

def firstPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input).map String.trim
  let some ⟨hraw⟩ := checkThat raw (fun z => 0 < z.size) | IO.exitWithError "Empty input"
  let some lines := getLines raw | IO.exitWithError "couldn't get lines"
  let some problems := lines.transpose | IO.exitWithError "Rows not all the same length"
  let some ops := raw[raw.size - 1].parse? (sepBy ws parseOp) | IO.exitWithError "parse error 2"

  let solns := problems.zipWith solveProb ops
  return solns.sum

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def splitBlocks (nums : Array String) : Option (Array₂ Nat) := do
  let mut out : Array₂ Nat := #[]
  let mut curblock : Array Nat := #[]
  for ln in nums do
    if ln == "" then
      out := out.push curblock
      curblock := #[]
    else
      let some n := ln.parse? digits | failure
      curblock := curblock.push n
  return out.push curblock

def secondPart (input : FilePath) : IO Nat := do
  let rawstrings := (← IO.FS.lines input)
  let some ⟨hrawstrings⟩ := checkThat rawstrings (fun z => 0 < z.size) | IO.exitWithError "Empty input"
  let raw := rawstrings.map String.toCharArray |>.take (rawstrings.size - 1)
  let some ⟨hraw⟩ := checkThat raw (fun z => 0 < z.size) | IO.exitWithError "Empty input"
  let some ops := rawstrings[rawstrings.size - 1].parse? (sepBy ws parseOp) | IO.exitWithError "parse error 2"
  let some rawt := raw.transpose | IO.exitWithError "Rows not all of same size"
  let rawtstrings := rawt.map String.ofCharArray |>.map String.trim
  let some problems := splitBlocks rawtstrings | IO.exitWithError "Error parsing blocks"
  let solns := problems.zipWith solveProb ops
  return solns.sum

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day06
