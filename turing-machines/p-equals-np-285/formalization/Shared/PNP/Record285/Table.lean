import Shared.Beeping.Machines

/-! The published transition bytes are embedded at elaboration, and decoded in
Lean. Executable finite checks inspect the ordered rows, bounds, and event mask;
they are not kernel proofs or evidence that the machine implements the source algorithm. -/
namespace Shared.PNP.Record285

open Shared.Beeping.Machines

/-- Exactly the file from producer db256d6ae59a47eb941a2f0c5cf3f37b3c4633c8. -/
def literal : String := include_str "events.tm"

structure RawRow where
  state : Nat
  read : Nat
  write : Nat
  move : Move
  next : Nat
  event : Nat
  deriving DecidableEq, Repr

/-- A kernel-reducible parser: delimiters are literal ASCII space and LF. -/
def splitChars (separator : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    let parts := splitChars separator cs
    if c == separator then [] :: parts
    else match parts with
      | [] => [[c]]
      | p :: ps => (c :: p) :: ps

def digit (c : Char) : Option Nat :=
  if c == '0' then some 0 else if c == '1' then some 1 else
  if c == '2' then some 2 else if c == '3' then some 3 else
  if c == '4' then some 4 else if c == '5' then some 5 else
  if c == '6' then some 6 else if c == '7' then some 7 else
  if c == '8' then some 8 else if c == '9' then some 9 else none

def decimal (cs : List Char) : Option Nat := do
  guard (!cs.isEmpty)
  cs.foldlM (fun n c => do let d ← digit c; pure (10*n+d)) 0

def parseRow (line : List Char) : Option RawRow := do
  match splitChars ' ' line with
  | [s,r,w,d,n,e] =>
    let s ← decimal s
    let r ← decimal r
    let w ← decimal w
    let d ← if d == ['L'] then some Move.left else if d == ['R'] then some Move.right else none
    let n ← decimal n
    let e ← decimal e
    some ⟨s,r,w,d,n,e⟩
  | _ => none

def parse : Option (List RawRow) := do
  let lines := splitChars '\n' literal.toList
  guard (lines.take 5 = ["#! format beeper-events-v1".toList, "#! states 285".toList,
    "#! start 0".toList, "#! blank 0".toList, "#! head 0".toList])
  let rest := lines.drop 5
  guard (rest.getLast? = some [])
  rest.dropLast.mapM parseRow

def wellFormed (rows : List RawRow) : Bool :=
  rows.length == 570 && (rows.zipIdx.all fun (row,i) =>
    row.state == i / 2 && row.read == i % 2 && row.write < 2 && row.next < 285 &&
    row.event == (if i == 243 then 1 else 0))

end Shared.PNP.Record285
