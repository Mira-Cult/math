import Shared.Beeping.TableBits

/-!
A total, kernel-reducible parser for a restricted `beeper-events-v1` format.
It accepts exactly the five ordered headers, single-space-separated fields,
nonnegative decimal head positions, ascending state numbers with the 0 row
immediately followed by the 1 row, and an optional final newline. Every
destination and the start must be in range. It can reject other valid
serializations of the broader format. It returns the shared raw-machine
representation; the fixtures below do not establish a universal parser
correctness theorem. It does not by itself identify any particular source
file or prove machine behavior.
-/
namespace Shared.Beeping.NPcoNP.Table284Ascii
open Shared.Beeping.TableBits

/-- Splitting into non-overlapping character fields, preserving empty fields. -/
def split (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: split sep cs
    else match split sep cs with
      | [] => [[c]]
      | x :: xs => (c :: x) :: xs

def digit (c : Char) : Option Nat :=
  if '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat then some (c.toNat - '0'.toNat) else none

def digitsAux (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs => do
    let d ← digit c
    digitsAux (10 * acc + d) cs

def nat (xs : List Char) : Option Nat :=
  if xs.isEmpty then none else digitsAux 0 xs

def bit : List Char → Option Bool
  | ['0'] => some false
  | ['1'] => some true
  | _ => none

/-- The raw move bit is false for left and true for right. -/
def move : List Char → Option Bool
  | ['L'] => some false
  | ['R'] => some true
  | _ => none

/-- Return source state, read symbol, and the complete fixed table row. -/
def row (s : List Char) : Option (Nat × Bool × RawRow) := do
  let [q,r,w,m,n,b] := split ' ' s | none
  let q ← nat q
  let r ← bit r
  let w ← bit w
  let m ← move m
  let n ← nat n
  let b ← bit b
  some (q,r,(w,(m,(n,b))))

/-- Check both rows of each source state, in ascending order. An empty last
field corresponds to a single final newline; other blank lines are rejected. -/
def rows (n : Nat) : Nat → List (List Char) → Option (List RawPair)
  | i, [] => if i = n then some [] else none
  | i, [[]] => if i = n then some [] else none
  | i, a :: b :: rest => do
    let (qa,ra,wa) ← row a
    let (qb,rb,wb) ← row b
    if i < n ∧ qa = i ∧ qb = i ∧ ra = false ∧ rb = true ∧
        wa.2.2.1 < n ∧ wb.2.2.1 < n then
      let tail ← rows n (i+1) rest
      some ((wa,wb) :: tail)
    else none
  | _, _ => none

/-- Read exactly `#! key value` using single space separators. -/
def header (key : List Char) (s : List Char) : Option (List Char) :=
  match split ' ' s with
  | [a,b,v] => if a = ['#','!'] ∧ b = key then some v else none
  | _ => none

/-- Parse character data from a full event table. Its returned state count is
the first component; `RawMachine` contains the checked start, blank, head,
and ordered row pairs. -/
def parseChars (input : List Char) : Option (Nat × RawMachine) := do
  let hformat :: hstates :: hstart :: hblank :: hhead :: rest := split '\n' input | none
  let format ← header ['f','o','r','m','a','t'] hformat
  if format ≠ ['b','e','e','p','e','r','-','e','v','e','n','t','s','-','v','1'] then none else do
    let n ← (header ['s','t','a','t','e','s'] hstates).bind nat
    let start ← (header ['s','t','a','r','t'] hstart).bind nat
    let blank ← (header ['b','l','a','n','k'] hblank).bind bit
    let head ← (header ['h','e','a','d'] hhead).bind nat
    if start < n then
      let rs ← rows n 0 rest
      some (n, ((start, (blank, (head : Int))), rs))
    else none

/-- The text wrapper uses Lean's string-to-character conversion. -/
def parse (s : String) : Option (Nat × RawMachine) := parseChars s.toList

namespace Fixtures
example : row "99 1 0 L 1 1".toList = some (99,true,(false,(false,(1,true)))) := by decide
example : row "99 2 0 L 1 1".toList = none := by decide
example : row "99 1 0 X 1 1".toList = none := by decide
example : row "99 1 0 L 1 2".toList = none := by decide
example : nat "-1".toList = none := by decide
example : nat "".toList = none := by decide

private def header1 : String :=
  "#! format beeper-events-v1\n#! states 1\n#! start 0\n#! blank 0\n#! head 0\n"

example : parse (header1 ++ "0 0 1 R 0 0\n0 1 0 L 0 1\n") =
    some (1, ((0,(false,0)), [((true,(true,(0,false))),(false,(false,(0,true))))])) := by rfl
example : parse (header1 ++ "0 0 1 R 0 0\n0 1 0 L 0 1") =
    some (1, ((0,(false,0)), [((true,(true,(0,false))),(false,(false,(0,true))))])) := by rfl
example : parse (header1 ++ "0 0 1 R 0 0\n0 0 0 L 0 1\n") = none := by decide
example : parse (header1 ++ "0 0 1 R 0 0\n") = none := by decide
example : parse (header1 ++ "0 0 1 R 1 0\n0 1 0 L 0 1\n") = none := by decide
example : parse (header1 ++ "0 0 1 R 0 0\n0 1 0 L 0 1\n\n") = none := by decide
example : parse "#! format beeper-v1\n#! states 1\n#! start 0\n#! blank 0\n#! head 0\n0 0 1 R 0 0\n0 1 0 L 0 1\n" = none := by decide
end Fixtures

end Shared.Beeping.NPcoNP.Table284Ascii
