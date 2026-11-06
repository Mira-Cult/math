import Shared.Beeping.NPcoNP.GrammarGraph284
import Shared.Beeping.NPcoNP.Swap284Sites

/-! Partial interpretation of producer register-graph rows. The grammar also
contains native-half instructions; these are deliberately rejected, not
misidentified as ordinary decrement. This module does not claim the generated
graph has any particular rows, nor that its outside rows are interpreted by
this decoder. -/
namespace Shared.Beeping.NPcoNP.GraphRegister284
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Swap284Register
open Shared.Beeping.NPcoNP.Swap284Sites
open PASoundness.RegisterMachine

/-- Read a canonical decimal register number (0 through 11) and the
remaining characters. Multi-digit cases precede the single digit 1. -/
def readRegister : List Char → Option (Fin 12 × List Char)
  | '1' :: '0' :: cs => some (⟨10, by decide⟩, cs)
  | '1' :: '1' :: cs => some (⟨11, by decide⟩, cs)
  | '0' :: cs => some (⟨0, by decide⟩, cs)
  | '1' :: cs => some (⟨1, by decide⟩, cs)
  | '2' :: cs => some (⟨2, by decide⟩, cs)
  | '3' :: cs => some (⟨3, by decide⟩, cs)
  | '4' :: cs => some (⟨4, by decide⟩, cs)
  | '5' :: cs => some (⟨5, by decide⟩, cs)
  | '6' :: cs => some (⟨6, by decide⟩, cs)
  | '7' :: cs => some (⟨7, by decide⟩, cs)
  | '8' :: cs => some (⟨8, by decide⟩, cs)
  | '9' :: cs => some (⟨9, by decide⟩, cs)
  | _ => none

/-- Resolve only an exact ordinary register operation spelling. -/
def ordinaryRegister (op suffix : String) : Option (Fin 12) := do
  let cs ← match op.toList with
    | '3' :: '.' :: '$' :: 'c' :: 'o' :: 'a' :: 'l' :: 'e' :: 's' :: 'c' :: 'e' :: 'd' :: '.' :: cs => some cs
    | _ => none
  let (r, rest) ← readRegister cs
  if rest == suffix.toList then some r else none

/-- Reject jump destinations outside the candidate 185-row graph. -/
def targetFin (n : Nat) : Option (Fin 185) :=
  if h : n < 185 then some ⟨n, h⟩ else none

/-- Partial decoder of ordinary increments, conditional decrements and beeps.
Malformed spelling/arity and out-of-range targets are rejected. In particular,
native-half rows do not decode as decrement. -/
def decodeRow (r : Row) : Option (Instruction 12 185) :=
  match r.targets with
  | [n] => do
      let next ← targetFin n
      if r.op == "beep" then pure ⟨.emit true, next, next⟩ else do
        let reg ← ordinaryRegister r.op ".inc"
        pure ⟨.inc reg, next, next⟩
  | [n,m] => do
      let yes ← targetFin n
      let no ← targetFin m
      let reg ← ordinaryRegister r.op ".decnz"
      pure ⟨.decNZ reg, yes, no⟩
  | _ => none

/-- A supplied register program agrees at every graph row decoded by this
partial decoder. Unsupported rows, including native-half, are unconstrained.
This is not a whole-graph implementation certificate. -/
def Compatible (g : Graph) (p : Program 12 185) : Prop :=
  ∀ (i : Fin 185) (row : Row) (inst : Instruction 12 185),
    g.rows[i.val]? = some row → decodeRow row = some inst → p.code[i] = inst

example : decodeRow ⟨"3.$coalesced.8.decnz", [72,73]⟩ =
    some ⟨.decNZ L, ⟨72, by decide⟩, ⟨73, by decide⟩⟩ := by rfl
example : decodeRow ⟨"3.$native-half:$coalesced.2.decnz", [71,72]⟩ = none := by rfl
example : decodeRow ⟨"3.$coalesced.8.inc", [185]⟩ = none := by rfl
example : decodeRow ⟨"3.$coalesced.8.decnz", [72]⟩ = none := by rfl

end Shared.Beeping.NPcoNP.GraphRegister284
