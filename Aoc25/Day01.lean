import Aoc25.Utils
namespace Day01

open System Std.Internal.Parsec.String

def testinput1 : FilePath := "input_01_test1"
def testinput2 : FilePath := "input_01_test2"
def realinput : FilePath := "input_01"

/-
PART 1:
-/

def parseRotation : Parser Int := do
  let d ← asciiLetter
  let n ← digits
  if d == 'L' then return -n else return n

def firstPart (input : FilePath) : IO Nat := do
  let raw : Option (Array Int) := (← IO.FS.lines input).mapM <| fun s => String.parse? s parseRotation
  let some rots := raw | IO.exitWithError "Parse error"
  let mut total := 0
  let mut pos := 50
  for rot in rots do
    pos := (pos + rot) % 100
    if pos == 0 then total := total + 1
  return total

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Int := do
  let raw : Option (Array Int):= (← IO.FS.lines input).mapM <| fun s => String.parse? s parseRotation
  let some rots := raw | IO.exitWithError "Parse error"
  let mut total : Int := 0
  let mut pos : Int := 50
  for rot in rots do
    total := total + rot.natAbs / 100
    let rot' := if rot ≥ 0 then rot % 100 else rot % 100 - 100
    if pos ≠ 0 ∧ pos + rot' ≤ (0 : Int) then total := total + 1
      else if pos ≠ 0 ∧ pos + rot' ≥ (100 : Int) then total := total + 1
    pos := (pos + rot') % 100
  return total

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day01
