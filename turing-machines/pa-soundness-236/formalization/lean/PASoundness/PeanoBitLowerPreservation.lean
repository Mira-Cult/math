import PASoundness.PeanoPowerDivisibilityClosed
import PASoundness.PeanoBitDivisiblePreserve
import PASoundness.PeanoBitDivisibleReverse

/-! PA preservation of bits below the exponent of an added power. -/
namespace PASoundness.PeanoBitLowerPreservation
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- PA proves both implications between the old and new bit predicates at
any index below the exponent of the added power. The powers are explicit
literal trace hypotheses; their existence is not asserted by this theorem.
Free variables 0,1,2,5,6 denote the upper exponent, lower exponent, lower
power, old code, and added upper power respectively. -/
theorem lower_bits_preserved : FormulaProves
    ((pow2 (.var 1) (.var 2)).imp
      ((pow2 (.var 0) (.var 6)).imp
        ((less (.var 1) (.var 0)).imp
          (((bitFormula (.var 5) (.var 1)).imp
              (bitFormula (add (.var 5) (.var 6)) (.var 1))) ⊓
            ((bitFormula (add (.var 5) (.var 6)) (.var 1)).imp
              (bitFormula (.var 5) (.var 1))))))) := by
  let P := pow2 (.var 1) (.var 2)
  let Q := pow2 (.var 0) (.var 6)
  let L := less (.var 1) (.var 0)
  let D := PeanoDivisibility.divides (add (.var 2) (.var 2)) (.var 6)
  let B := bitFormula (.var 5) (.var 1)
  let B' := bitFormula (add (.var 5) (.var 6)) (.var 1)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [L,Q,P]
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hq : FOL.Context Peano.Axiom Γ Q := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := .head _ _
  have hd : FOL.Context Peano.Axiom Γ D := by
    have h := PeanoPowerDivisibilityClosed.body_proved
    change FormulaProves (P.imp (Q.imp (L.imp D))) at h
    exact .mp (.mp (.mp (.closed h) hp) hq) hl
  have hforward : FOL.Context Peano.Axiom Γ (B.imp B') :=
    .mp (.mp (.closed PeanoBitDivisiblePreserve.preserve_bit_of_divides) hd) hp
  have hreverse : FOL.Context Peano.Axiom Γ (B'.imp B) :=
    .mp (.mp (.closed PeanoBitDivisibleReverse.reverse_bit_of_divides) hd) hp
  exact FOL.Context.conjunctionIntro hforward hreverse

end PASoundness.PeanoBitLowerPreservation

#print axioms PASoundness.PeanoBitLowerPreservation.lower_bits_preserved
