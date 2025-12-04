import Aoc25.Utils

open System Std.Internal.Parsec Std.Internal.Parsec.String

namespace Day03

def testinput1 : FilePath := "input_03_test1"
def testinput2 : FilePath := "input_03_test2"
def realinput : FilePath := "input_03"

/-
PART 1:
-/

def parseBank : Parser (Array Nat) := do
  let ds ← many digit
  return ds.map Char.toNatDigit

def calcBank (bank : Array Nat) (hbank : 0 < bank.size) : Nat := Id.run do
  let n := bank.size
  let mut prev := bank[0]
  let mut best := 0
  for hi : i in 1...<n do
    let cur := 10*prev + bank[i]
    if cur > best then best := cur
    prev := max prev bank[i]
  return best

def firstPart (input : FilePath) : IO Nat := do
  let some banks := (← IO.FS.lines input).mapM <| fun s => String.parse? s parseBank
    | IO.exitWithError "Parse error"
  let mut total := 0
  for bank in banks do
    let some ⟨hbank⟩ := checkThat bank (fun z => 0 < z.size) | IO.exitWithError "Trivial bank"
    total := total + calcBank bank hbank
  return total

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def calcBank₂ (bank : Array Nat) (hbank : 0 < bank.size) : Nat := Id.run do
  -- dp[i, j] := biggest joltage with i+1 batteries up to position j
  let n := bank.size
  let mut dp : Array (Array Nat) := #[]
  let mut firstrow := #[bank[0]]
  for hj : j in 1...<n do
    firstrow := firstrow.push <| max firstrow[j-1]! bank[j]
  dp := dp.push firstrow
  for hi : i in 1...=(11 : Nat) do
    let mut currow := Array.replicate i 0
    for hj : j in i...<n do
      let curbest := max (10*dp[i-1]![j-1]! + bank[j]) currow[j-1]!
      currow := currow.push curbest
    dp := dp.push currow
  let mut best := 0
  for hj : j in 1...<n do
    if best < dp[11]![j]! then best := dp[11]![j]!
  return best

def secondPart (input : FilePath) : IO Nat := do
  let some banks := (← IO.FS.lines input).mapM <| fun s => String.parse? s parseBank
    | IO.exitWithError "Parse error"
  let mut total := 0
  for bank in banks do
    let some ⟨hbank⟩ := checkThat bank (fun z => 0 < z.size) | IO.exitWithError "Trivial bank"
    let cur := calcBank₂ bank hbank
    total := total + cur
  return total

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day03
