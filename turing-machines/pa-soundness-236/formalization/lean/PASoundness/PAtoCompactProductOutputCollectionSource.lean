import PASoundness.PAtoCompactProductOutputCollectionCandidate
import PASoundness.PAtoCompactProductMatchCollectionConditional
import PASoundness.PAtoCompactScopedActiveReplace

/-! Specialize the transported-product candidate-prefix collection at the
actual source output domain 0. The source matrix, output bijection and source
candidate remain explicit. This is a guarded path graph, not yet a product
matrix or full output-transport proof. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputCollectionSource

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputInductionFixture
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional PASoundness.PAtoCompactProductOutputCollectionCandidate

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceFrame : Formula := .imp assumptions (.imp
  (PAtoCompactProductMatchCollectionConditional.candidateFormula 70)
  (.ex 58 (replace 59 70 partialInvariant)))
def actualFrame : Formula := .imp assumptions (.imp
  (PAtoCompactProductMatchCollectionConditional.candidateFormula 0)
  (.ex 58 (replace 59 0 partialInvariant)))

theorem source_frame_fresh : 70 ∉ sourceFrame.binders ∧ 0 ∉ sourceFrame.binders := by decide
theorem source_substitution : replace 70 0 sourceFrame = actualFrame := by decide

/-- The same represented output graph satisfies the guarded path invariant
on source domain 0 when that source has the stated candidate code. -/
noncomputable def source_collection : KDerivation (imp assumptions.encode
    (imp (candidateCode 0 81 77 78 72 64 73 59 75)
      (existsCode 58 (replace 59 0 partialInvariant).encode))) := by
  have h : KDerivation sourceFrame.encode := by
    simpa only [sourceFrame, CompactNamed.Formula.encode,
      PAtoCompactProductMatchCollectionConditional.candidate_formula_code, candidatePrefix] using candidate_collection
  have hi := replace_derivation 70 0 sourceFrame source_frame_fresh.1 source_frame_fresh.2 h
  rw [source_substitution] at hi
  simpa only [actualFrame, CompactNamed.Formula.encode,
    PAtoCompactProductMatchCollectionConditional.candidate_formula_code] using hi

theorem source_collection_certificate : theoremCode (certificate source_collection) =
    imp assumptions.encode (imp (candidateCode 0 81 77 78 72 64 73 59 75)
      (existsCode 58 (replace 59 0 partialInvariant).encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputCollectionSource

#print axioms PASoundness.PAtoCompactProductOutputCollectionSource.source_frame_fresh
#print axioms PASoundness.PAtoCompactProductOutputCollectionSource.source_substitution
#print axioms PASoundness.PAtoCompactProductOutputCollectionSource.source_collection
#print axioms PASoundness.PAtoCompactProductOutputCollectionSource.source_collection_certificate
