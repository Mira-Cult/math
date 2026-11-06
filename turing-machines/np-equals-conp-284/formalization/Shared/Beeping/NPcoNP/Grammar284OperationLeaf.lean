import Shared.Beeping.NPcoNP.Grammar284Quoted

/-! A total parser and renderer for the exact fixed indentation of an
unescaped operation leaf in the producer's JSON layout. This handles one
operation leaf and an arbitrary trailing character list; it is not a complete
JSON parser, grammar parser, or proof about the included producer bytes. -/

namespace Shared.Beeping.NPcoNP.Grammar284OperationLeaf
open Shared.Beeping.NPcoNP.Grammar284Quoted

/-- Remove an exact character opening, failing when it is absent. -/
def strip : List Char → List Char → Option (List Char)
  | [], s => some s
  | _ :: _, [] => none
  | c :: cs, d :: ds => if c = d then strip cs ds else none

theorem strip_append (opening tail : List Char) :
    strip opening (opening ++ tail) = some tail := by
  induction opening with
  | nil => rfl
  | cons c cs ih => simp [strip, ih]

def opening : List Char := "      {\n        \"op\": \"".toList

def suffix : List Char := "\n      }".toList

/-- The operation-leaf layout agrees with the exact field indentation used
in the pinned producer file, provided the name requires no escaping. -/
def render (name : List Char) : List Char :=
  opening ++ name ++ '"' :: suffix

def parse (input : List Char) : Option (List Char × List Char) := do
  let rest ← strip opening input
  let (name, rest) ← scan rest
  let tail ← strip suffix rest
  some (name, tail)

/-- Every safe name round-trips with an arbitrary following character list. -/
theorem parse_render (name tail : List Char) (hs : safe name = true) :
    parse (render name ++ tail) = some (name, tail) := by
  simp [parse, render, List.append_assoc, strip_append,
    scan_append_quote name (suffix ++ tail) hs]

example : parse (render "3.$coalesced.10.inc".toList ++ ",\n".toList) =
    some ("3.$coalesced.10.inc".toList, ",\n".toList) := by decide
example : parse "invalid".toList = none := by decide
example : parse "      {\n        \"op\": \"abc\"\n      !".toList = none := by decide

end Shared.Beeping.NPcoNP.Grammar284OperationLeaf
