import PASoundness.PAtoCompactAdditionCleanEquivWitness
import PASoundness.PAtoCompactSuffixCleanGraphGuard
import PASoundness.PAtoCompactScopedActiveReplace

/-! Relocate the existing clean-isomorphism witness construction to the
common source and suffix labels used by the seeded span. The supplied suffix
equivalence remains an object-level antecedent. No candidate assumption on
the source or suffix is introduced. -/
namespace PASoundness.PAtoCompactSuffixCleanWitness

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionCleanEquivWitness PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactSuffixCleanGraphGuard

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def suffixBijection : Formula := replace 25 1 (replace 1 31 (replace 0 25 bijectionFormula))
def suffixOrder : Formula := replace 25 1 (replace 1 31 (replace 0 25 orderFormula))
def suffixEquivalence : Formula := .ex 6 (namedBoth suffixBijection suffixOrder)
def cleanMatrix : Formula := namedBoth (namedBoth suffixBijection suffixOrder) storedClean

private def oldMatrix : Formula := namedBoth
  (namedBoth (replace 1 34 (replace 0 31 bijectionFormula))
    (replace 1 34 (replace 0 31 orderFormula)))
  (.all 19 (.imp (.member 6 19) (edgePredicate 19 31 34)))
private def sourceFrame : Formula := .imp (equivAt 31 34) (.ex 6 oldMatrix)
private def sourceMoved : Formula := replace 31 1 sourceFrame

/-- Given the actual common-source-to-suffix equivalence, K constructs one
graph satisfying both its isomorphism matrix and stored-pair cleanliness. -/
def suffix_clean_witness : KDerivation
    (imp suffixEquivalence.encode (existsCode 6 cleanMatrix.encode)) := by
  have hbase : KDerivation sourceFrame.encode := by
    simpa only [sourceFrame,oldMatrix,Formula.encode] using clean_equiv_witness
  have hsource := replace_derivation 31 1 sourceFrame (by decide) (by decide) hbase
  have htarget := replace_derivation 34 31 sourceMoved (by decide) (by decide)
    (by simpa only [sourceMoved] using hsource)
  have halign : replace 34 31 sourceMoved =
      .imp suffixEquivalence (.ex 6 cleanMatrix) := by decide
  rw [halign] at htarget
  exact htarget

theorem suffix_clean_witness_certificate : theoremCode (certificate suffix_clean_witness) =
    imp suffixEquivalence.encode (existsCode 6 cleanMatrix.encode) :=
  certificate_correct suffix_clean_witness

end PASoundness.PAtoCompactSuffixCleanWitness

#print axioms PASoundness.PAtoCompactSuffixCleanWitness.suffixBijection
#print axioms PASoundness.PAtoCompactSuffixCleanWitness.suffixOrder
#print axioms PASoundness.PAtoCompactSuffixCleanWitness.suffixEquivalence
#print axioms PASoundness.PAtoCompactSuffixCleanWitness.cleanMatrix
#print axioms PASoundness.PAtoCompactSuffixCleanWitness.suffix_clean_witness
#print axioms PASoundness.PAtoCompactSuffixCleanWitness.suffix_clean_witness_certificate
