import Aoc25.Utils
import Aoc25.Direction

open System Std.Internal.Parsec.String

/-
Input grid: 136×136
-/

namespace Day04

def testinput1 : FilePath := "input_04_test1"
def testinput2 : FilePath := "input_04_test2"
def realinput : FilePath := "input_04"

/-
PART 1:
-/

def eightNeighbours : Array (List NSEW) := #[[.n, .w], [.n], [.n, .e], [.w], [.e], [.s, .w], [.s], [.s, .e]]

def isRemovable (grid : Vector₂ Char n m) (pos : Int × Int) : Bool := Id.run do
  let mut nhrolls := 0
  for nh in eightNeighbours do
    let ⟨i', j'⟩ := NSEW.walk nh pos.1 pos.2
    if grid.get₂? i' j' == some '@' then nhrolls := nhrolls + 1
  if grid.get₂? pos.1 pos.2 = some '@' ∧ nhrolls < 4 then return true
  return false

def firstPart (input : FilePath) : IO Nat := do
  let rawgrid := (← IO.FS.lines input).map String.toCharArray
  let some ⟨n, m, grid⟩ := rawgrid.toVector₂ | IO.exitWithError "Grid not rectangular"
  let mut total := 0
  for _hi : i in (0 : Int)...<n do
    for _hj : j in (0 : Int)...<m do
      if isRemovable grid (i, j) then
        total := total + 1
  return total

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  let rawgrid := (← IO.FS.lines input).map String.toCharArray
  let some ⟨n, m, grid⟩ := rawgrid.toVector₂ | IO.exitWithError "Grid not rectangular"
  let mut removables : Array (Int × Int) := #[]
  let mut gr := grid
  for _hi : i in (0 : Int)...<n do
    for _hj : j in (0 : Int)...<m do
      if isRemovable grid (i, j) then
        removables := removables.push (i, j)
  let mut total := 0
  while h : removables.size > 0 do
    let ⟨i, j⟩ := removables[removables.size - 1]
    removables := removables.pop
    if gr.get₂? i j = some '@' ∧ isRemovable gr (i, j) then
      gr := gr.setIfInBounds i j '.'
      total := total + 1
      for nh in eightNeighbours do
        let ⟨i', j'⟩ := NSEW.walk nh i j
        if gr.get₂? i' j' = some '@' then removables := removables.push (i', j')
  return total

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day04
