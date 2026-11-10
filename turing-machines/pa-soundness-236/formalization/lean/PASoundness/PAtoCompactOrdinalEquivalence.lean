import PASoundness.PAtoCompactStandardReflexivity
import PASoundness.PAtoCompactIsomorphismRigidityClosed

/-! Standard-HF calibration of the concrete proposed quotient equality on
finite ordinal codes. This is not a K proof of quotient laws, a proof
translation, or a PA soundness bridge. -/
namespace PASoundness.PAtoCompactOrdinalEquivalence
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactStandardReflexivity
open PASoundness.PAtoCompactIsomorphismRigidityClosed
open PASoundness.CompactMatrix (Environment)
open PASoundness.HFCoding

/-- On standard finite ordinals, the literal compact formula for the
proposed isomorphism equality is true exactly when the indices agree. -/
theorem standard_ordinal_iff (ρ : Environment) (n m : Nat)
    (h0 : ρ 0 = (ordinal n).code) (h1 : ρ 1 = (ordinal m).code) :
    (PASoundness.CompactMatrix.decode equivalentFormula.encode).Realize ρ ↔ n = m := by
  rw [Formula.encode_realize]
  constructor
  · exact ordinal_rigidity ρ n m h0 h1
  · intro h
    apply standard_reflexive ρ
    rw [h] at h0
    exact h0.trans h1.symm

end PASoundness.PAtoCompactOrdinalEquivalence

#print axioms PASoundness.PAtoCompactOrdinalEquivalence.standard_ordinal_iff
