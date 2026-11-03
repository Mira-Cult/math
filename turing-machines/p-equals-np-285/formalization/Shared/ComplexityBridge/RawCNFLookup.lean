import Shared.ComplexityBridge.TM2NumeralPairCompare
import Shared.ComplexityBridge.TM2LiteralParse

namespace Shared.ComplexityBridge.RawCNFLookup
open Shared.ComplexityBridge

/-- First occurrence wins; a short witness or missing variable yields false.
Equality uses the executable finite-bit comparator, including noncanonical names. -/
def lookup : List (List Bool) → List Bool → List Bool → Bool
  | [], _, _ => false
  | _::_, [], _ => false
  | v::vs, b::bs, target =>
      if TM2NumeralPairCompare.answer (target,v) then b else lookup vs bs target

theorem lookup_correct (vars : List (List Bool)) (bits target : List Bool) :
    lookup vars bits target =
      CNF.assignment (vars.map Computability.decodeNat) bits (Computability.decodeNat target) := by
  induction vars generalizing bits with
  | nil => cases bits <;> rfl
  | cons v vs ih =>
    cases bits with
    | nil => rfl
    | cons b bs =>
      by_cases h : Computability.decodeNat target = Computability.decodeNat v
      · have ha := (TM2NumeralPairCompare.answer_correct target v).2 h
        simp [lookup,CNF.assignment,h,ha]
      · have ha : TM2NumeralPairCompare.answer (target,v) = false := by
          cases hc : TM2NumeralPairCompare.answer (target,v) with
          | false => rfl
          | true => exact False.elim (h ((TM2NumeralPairCompare.answer_correct target v).1 hc))
        simp [lookup,CNF.assignment,h,ha,ih]

/-- A parsed literal and the raw lookup agree with the canonical evaluation. -/
theorem eval_literal_correct (input nameBits : List Bool) (sign : Bool)
    (h : TM2LiteralParse.literalBits input = some (nameBits,sign))
    (vars : List (List Bool)) (bits : List Bool) :
    (BitstringEncoding.bitDecode input : Option CNF.Literal) = some (Computability.decodeNat nameBits,sign) ∧
    (lookup vars bits nameBits == sign) =
      CNF.evalLiteral (CNF.assignment (vars.map Computability.decodeNat) bits) (Computability.decodeNat nameBits,sign) := by
  constructor
  · rw [TM2LiteralParse.literalBits_decode,h]; rfl
  · simp [CNF.evalLiteral,lookup_correct]

namespace Fixtures
example : lookup [[false],[false,true]] [true,false] [false,true] = true := by decide
example : lookup [[false],[false,true]] [false,true] [false] = false := by decide
example : lookup [[false]] [] [false] = false := by decide
example : lookup [] [true] [] = false := by decide
end Fixtures

end Shared.ComplexityBridge.RawCNFLookup
