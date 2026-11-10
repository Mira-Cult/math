import PASoundness.PAtoCompactSecondAdditionCleanSuffixWitness

/-! Preserve the second addition's actual cut and suffix while constructing
one clean source-to-suffix isomorphism graph in K. -/
namespace PASoundness.PAtoCompactSecondAdditionCleanSuffix

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSecondAdditionCutAllocation
open PASoundness.PAtoCompactSecondAdditionCleanSuffixWitness

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def strengthenedBody : Formula := namedBoth allocatedBody (.ex 7 cleanMatrix)
def output : Formula := .ex 41 (.ex 38 strengthenedBody)

/-- The second cut and suffix stay paired with the graph constructed from
that same suffix's own equivalence. -/
def second_addition_clean_suffix : KDerivation (imp addition.encode output.encode) := by
  have hpoint : KDerivation (imp allocatedBody.encode strengthenedBody.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [allocatedBody.encode]
    have hb : Context Γ allocatedBody.encode := .head _ _
    have he : Context Γ suffixEquivalence38.encode :=
      Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hb))
    have hg : Context Γ (existsCode 7 cleanMatrix.encode) := .mp he (.closed second_clean_suffix_witness)
    exact Context.conjunctionIntro hb hg
  have hw := existsCongr 41 (existsCongr 38 hpoint)
  simpa only [allocated,output,Formula.encode] using compose allocate_second_addition hw

theorem second_addition_clean_suffix_certificate : theoremCode (certificate second_addition_clean_suffix) =
    imp addition.encode output.encode := certificate_correct second_addition_clean_suffix

end PASoundness.PAtoCompactSecondAdditionCleanSuffix

#print axioms PASoundness.PAtoCompactSecondAdditionCleanSuffix.strengthenedBody
#print axioms PASoundness.PAtoCompactSecondAdditionCleanSuffix.output
#print axioms PASoundness.PAtoCompactSecondAdditionCleanSuffix.second_addition_clean_suffix
#print axioms PASoundness.PAtoCompactSecondAdditionCleanSuffix.second_addition_clean_suffix_certificate
