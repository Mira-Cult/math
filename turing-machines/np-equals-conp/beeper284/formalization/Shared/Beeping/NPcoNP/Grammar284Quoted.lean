import Shared.Beeping.NPcoNP.Grammar284Data

/-! A total, quote-delimited scanner for the restricted unescaped strings used
by the generated grammar. This is not a general JSON string parser: escaping,
Unicode normalization, malformed byte handling, and the surrounding JSON
syntax are outside its interface. In particular this module does not establish
that the generated AST equals the pinned producer bytes. -/

namespace Shared.Beeping.NPcoNP.Grammar284Quoted
open Shared.Beeping.NPcoNP.Grammar284

/-- Characters that can occur literally in a JSON string without escaping. -/
def safeChar (c : Char) : Bool := c != '"' && c != '\\' && c.toNat ≥ 32

def safe (s : List Char) : Bool := s.all safeChar

def render (s : List Char) : List Char := '"' :: s ++ ['"']

/-- Scan the remainder of a quote-delimited string, returning the tail after
its closing quote. The caller supplies the unescaped-string precondition. -/
def scan : List Char → Option (List Char × List Char)
  | [] => none
  | '"' :: rest => some ([], rest)
  | c :: rest => (scan rest).map (fun (s, rest) => (c :: s, rest))

def parse : List Char → Option (List Char × List Char)
  | '"' :: rest => scan rest
  | _ => none

/-- The scanner returns the first unescaped quoted payload and arbitrary
remaining input whenever the payload contains only safe characters. -/
theorem scan_append_quote (s tail : List Char)
    (h : safe s = true) : scan (s ++ '"' :: tail) = some (s, tail) := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    simp only [safe, List.all_cons, Bool.and_eq_true] at h
    have hc : c ≠ '"' := by
      have hh := h.1
      simp only [safeChar, Bool.and_eq_true, bne_iff_ne] at hh
      exact hh.1.1
    simp only [List.cons_append]
    cases c with
    | mk v =>
      simp only [scan, ih h.2, Option.map_some]

theorem parse_render (s tail : List Char) (h : safe s = true) :
    parse (render s ++ tail) = some (s, tail) := by
  simp only [render, List.cons_append, List.append_assoc, parse]
  exact scan_append_quote s tail h

def safeLeaf : Leaf → Bool
  | .node _ => true
  | .op s => safe s.toList

set_option maxRecDepth 4096 in
/-- Every operation name in the literal AST can be rendered without JSON
string escapes. This concerns the Lean AST, not the original JSON bytes. -/
theorem producer_operations_safe :
    producerGrammar.nodes.toList.all (fun (a, b) => safeLeaf a && safeLeaf b) = true := by
  decide

set_option maxRecDepth 4096 in
/-- Every register name in the literal AST can be rendered without JSON
string escapes. -/
theorem producer_registers_safe :
    producerGrammar.registers.toList.all (fun s => safe s.toList) = true := by
  decide

example : parse (render "abc".toList ++ "tail".toList) =
    some ("abc".toList, "tail".toList) := by decide
example : parse "\"unterminated".toList = none := by decide
example : safe "a\"b".toList = false := by decide
example : safe "a\\b".toList = false := by decide
example : safe ['\n'] = false := by decide

end Shared.Beeping.NPcoNP.Grammar284Quoted
