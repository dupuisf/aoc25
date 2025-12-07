import Aoc25.Utils

open System Std.Internal.Parsec.String Std.Internal.Parsec

-- Grid: 142 rows, 141 cols

namespace Day07

def testinput1 : FilePath := "input_07_test1"
def realinput : FilePath := "input_07"

/-
PART 1:
-/

def firstPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let some ⟨n, m, grid⟩ := Vector₂.getGrid raw (many <| oneOf #['.', '^', 'S'])
    | IO.exitWithError "parse error"
  let some ⟨hn⟩ := checkThat n (fun x => 0 < x) | IO.exitWithError "n = 0"

  let mut state := grid[0].map fun x => if x == '.' then false else true
  let mut ans := 0
  for hrow : row in 1...<n do
    for hi : i in 0...<m do
      if state[i] && grid[row][i] == '^' then
        ans := ans + 1
        state := state.setIfInBounds (i-1) true
        state := state.setIfInBounds (i+1) true
        state := state.set i false
  return ans

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let some ⟨n, m, grid⟩ := Vector₂.getGrid raw (many <| oneOf #['.', '^', 'S'])
    | IO.exitWithError "parse error"
  let some ⟨hn⟩ := checkThat n (fun x => 0 < x) | IO.exitWithError "n = 0"

  -- `state[i]` is the number of timelines that end up at `i`
  let mut state := grid[0].map fun x => if x == '.' then 0 else 1
  let mut ans := 0
  for hrow : row in 1...<n do
    let mut newstate := Vector.replicate m 0
    for hi : i in 0...<m do
      if grid[row][i] == '.' then
        newstate := newstate.set i (newstate[i] + state[i])
      else
        if i = 0 then
          newstate := newstate.set! (i+1) (newstate[i+1]! + state[i])
        else
          newstate := newstate.set! (i+1) (newstate[i+1]! + state[i])
          newstate := newstate.set! (i-1) (newstate[i-1]! + state[i])
    state := newstate
  return state.sum

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day07
