import PASoundness.PAtoCompactFirstAdditionCutAllocation

/-! Preserve the first addition's actual cut and suffix while constructing
one clean source-to-suffix isomorphism graph in K. -/
namespace PASoundness.PAtoCompactFirstAdditionCleanSuffix

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuffixCleanWitness
open PASoundness.PAtoCompactFirstAdditionCutAllocation

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def strengthenedBody : Formula := namedBoth allocatedBody (.ex 6 cleanMatrix)
def output : Formula := .ex 40 (.ex 31 strengthenedBody)

/-- The original addition cut and suffix remain paired with the clean graph
constructed from that suffix's own equivalence. -/
def first_addition_clean_suffix : KDerivation (imp addition.encode output.encode) := by
  have hpoint : KDerivation (imp allocatedBody.encode strengthenedBody.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [allocatedBody.encode]
    have hb : Context Γ allocatedBody.encode := .head _ _
    have he : Context Γ suffixEquivalence.encode :=
      Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hb))
    have hg : Context Γ (existsCode 6 cleanMatrix.encode) := .mp he (.closed suffix_clean_witness)
    exact Context.conjunctionIntro hb hg
  have hw := existsCongr 40 (existsCongr 31 hpoint)
  simpa only [allocated,output,Formula.encode] using compose allocate_first_addition hw

theorem first_addition_clean_suffix_certificate : theoremCode (certificate first_addition_clean_suffix) =
    imp addition.encode output.encode := certificate_correct first_addition_clean_suffix

end PASoundness.PAtoCompactFirstAdditionCleanSuffix

#print axioms PASoundness.PAtoCompactFirstAdditionCleanSuffix.strengthenedBody
#print axioms PASoundness.PAtoCompactFirstAdditionCleanSuffix.output
#print axioms PASoundness.PAtoCompactFirstAdditionCleanSuffix.first_addition_clean_suffix
#print axioms PASoundness.PAtoCompactFirstAdditionCleanSuffix.first_addition_clean_suffix_certificate
