import PASoundness.PeanoAX8LiteralPermutation
import PASoundness.PeanoAX8RenamedFresh

/-! Derivation of the literal arithmetic AX8 formula for three distinct
names, using a checked finite standardizing permutation. -/
namespace PASoundness.PeanoAX8Distinct
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactLogicalTransport
open PeanoFreeNamePermutation

/-- For `a ≠ b` and the source's guards `c ≠ a,b`, PA derives the actual
literal comprehension formula. The same derivation is transported back from
canonical names by the inverse swaps; no metatheoretic soundness is used.
The separate alias case `a = b` is not covered here. -/
theorem distinct_comprehension (a b c : Nat)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    FormulaProves (comprehensionFormula a b c) := by
  obtain ⟨xs, ha, hb, hc, hf⟩ := PeanoAX8RenamedFresh.distinct_fresh
    (interpreted c) a b c hab (Ne.symm hca) (Ne.symm hcb)
    (PeanoAX8DecodedFresh.interpreted_self_fresh c)
  let ρ := applyFormula xs (interpreted c)
  have hcanonical : FormulaProves (PeanoAX8CanonicalFormula.canonicalFormula ρ) :=
    PeanoAX8CanonicalFormula.canonical_formula ρ
      (hf 0 (by decide)) (hf 1 (by decide)) (hf 2 (by decide)) (hf 3 (by decide))
  have hrenamed : FormulaProves (applyFormula xs (comprehensionFormula a b c)) := by
    rw [PeanoAX8LiteralPermutation.literal_permutation xs a b c ha hb hc]
    exact hcanonical
  have hback := PeanoFreeNamePermutation.applyFormula_proves xs.reverse _ hrenamed
  rw [PeanoFreeNamePermutationInverse.reverse_applyFormula] at hback
  exact hback

end PASoundness.PeanoAX8Distinct

#print axioms PASoundness.PeanoAX8Distinct.distinct_comprehension
