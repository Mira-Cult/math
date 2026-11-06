import Shared.Beeping.NPcoNP.Grammar284OperationLeaf

/-! Total restricted node-leaf parser; this is not a full grammar parser. -/
namespace Shared.Beeping.NPcoNP.Grammar284NodeLeaf
open Shared.Beeping.NPcoNP.Grammar284OperationLeaf (strip strip_append)

def scanLine : List Char → Option (List Char × List Char)
  | [] => none
  | '\n' :: rest => some ([], rest)
  | c :: rest => (scanLine rest).map (fun (s, rest) => (c :: s, rest))

theorem scanLine_append (s tail : List Char) (h : '\n' ∉ s) :
    scanLine (s ++ '\n' :: tail) = some (s, tail) := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.cons_append]
    have hc : c ≠ '\n' := Ne.symm h.1
    simp [scanLine, hc, ih h.2]

theorem digit_no_line (n : Nat) : '\n' ∉ Nat.toDigits 10 n := by
  intro h
  have hh := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) h
  contradiction

theorem digit_all (n : Nat) : (Nat.toDigits 10 n).all Char.isDigit = true := by
  simp only [List.all_eq_true]
  intro c hc
  exact Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc

def readDigits (s : List Char) : Option Nat :=
  if s.isEmpty || !(s.all Char.isDigit) then none else
    let n := Nat.ofDigitChars 10 s 0
    if s == Nat.toDigits 10 n then some n else none

theorem readDigits_repr (n : Nat) : readDigits (Nat.toDigits 10 n) = some n := by
  simp [readDigits, Nat.toDigits_ne_nil, digit_all]

/-- Parse a canonical decimal line and leave its arbitrary suffix. -/
def parseLine (input : List Char) : Option (Nat × List Char) := do
  let (ds, tail) ← scanLine input
  let n ← readDigits ds
  some (n, tail)

theorem parseLine_repr (n : Nat) (tail : List Char) :
    parseLine (Nat.toDigits 10 n ++ '\n' :: tail) = some (n, tail) := by
  simp [parseLine, scanLine_append _ _ (digit_no_line n), readDigits_repr]

def opening : List Char := "      {\n        \"node\": ".toList
def suffix : List Char := "      }".toList

def render (n : Nat) : List Char := opening ++ Nat.toDigits 10 n ++ '\n' :: suffix

def parse (input : List Char) : Option (Nat × List Char) := do
  let rest ← strip opening input
  let (ds, rest) ← scanLine rest
  let n ← readDigits ds
  let tail ← strip suffix rest
  some (n, tail)

theorem parse_render (n : Nat) (tail : List Char) :
    parse (render n ++ tail) = some (n, tail) := by
  simp [parse, render, List.append_assoc, strip_append,
    scanLine_append _ _ (digit_no_line n), readDigits_repr]

example : parse (render 123 ++ ",\n".toList) = some (123, ",\n".toList) := by decide
example : parse "      {\n        \"node\": -1\n      }".toList = none := by decide
example : readDigits "01".toList = none := by decide
end Shared.Beeping.NPcoNP.Grammar284NodeLeaf
