import Aoc25.Utils

open System Std.Internal.Parsec.String

namespace Day02

def testinput1 : FilePath := "input_02_test1"
def testinput2 : FilePath := "input_02_test2"
def realinput : FilePath := "input_02"

/-
PART 1:
-/

def parseRange : Parser (Nat × Nat) := do
  let l ← digits
  let _ ← pchar '-'
  let r ← digits
  return ⟨l, r⟩

def isInvalid (n : Nat) : Bool := Id.run do
  let ds := n.toNatDigits
  if ds.size % 2 == 1 then return false
  let k := ds.size / 2
  for h : i in 0...<k do
    if ds[i] != ds[i + k] then return false
  return true

def firstPart (input : FilePath) : IO Nat := do
  let some ranges := (← IO.FS.readFile input).parse? (sepBy (pchar ',') parseRange)
    | IO.exitWithError "Parse error"
  --for ⟨l, r⟩ in ranges do
  --  IO.println (r - l)
  let mut total := 0
  for ⟨l, r⟩ in ranges do
    for n in l...=r do
      if isInvalid n then total := total + n
  return total

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def isInvalidMod (m n : Nat) : Bool := Id.run do
  let ds := n.toNatDigits
  if ds.size % m != 0 then return false
  let k := ds.size / m
  for i in 0...<k do
    for j in 0...<m do
      if ds[i]! != ds[i + j*k]! then return false
  return true

def isInvalid₂ (n : Nat) : Bool := Id.run do
  for i in 2...=(10 : Nat) do
    if isInvalidMod i n then return true
  return false

def secondPart (input : FilePath) : IO Nat := do
  let some ranges := (← IO.FS.readFile input).parse? (sepBy (pchar ',') parseRange)
    | IO.exitWithError "Parse error"
  let mut total := 0
  --for ⟨l, r⟩ in ranges do
  --  IO.println (Nat.log10 r)
  for ⟨l, r⟩ in ranges do
    for n in l...=r do
      if isInvalid₂ n then total := total + n
  return total

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day02
