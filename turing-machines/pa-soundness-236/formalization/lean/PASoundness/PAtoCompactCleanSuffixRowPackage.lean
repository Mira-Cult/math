import PASoundness.PAtoCompactMultiplicationSuffixCleanExists
import PASoundness.PAtoCompactFixedFirstRowClosed
import PASoundness.PAtoCompactCandidateWitness

/-! Package a clean suffix isomorphism and the full-prefix row invariant with
the SAME map graph. The row proof is an explicit proof-data input until its
capture-safe target-name specialization is supplied. This is a K construction,
not a product matrix, multiplication totality or a PA interpretation. -/
namespace PASoundness.PAtoCompactCleanSuffixRowPackage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateWitness PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFixedFirstRestrictedInduction
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationSuffixCleanExists
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

def candidate : Nat := candidateCode 31 213 209 210 202 0 203 205 206

def suffixBijection : Formula := replace 1 40 (replace 0 31 bijectionFormula)
def suffixOrder : Formula := replace 1 40 (replace 0 31 orderFormula)
def cleanMatrix : Formula := namedBoth (namedBoth suffixBijection suffixOrder) suffixClean
def rowResult : Formula := replace 0 31 predicate

/-- One graph 6 has the entire clean isomorphism matrix and is used by the
full-prefix row graph introduced inside the same existential scope. -/
def result : Formula := .ex 6 (namedBoth cleanMatrix rowResult)

/-- This constructor retains the candidate-to-row proof as an explicit input.
In particular, the theorem does not infer a row graph from cleanliness alone. -/
def package_of_row
    (row : KDerivation (imp candidate (imp suffixBijection.encode rowResult.encode))) :
    KDerivation (imp candidate (imp (equivAt 31 40).encode result.encode)) := by
  have hpoint : KDerivation (imp candidate (imp cleanMatrix.encode
      (namedBoth cleanMatrix rowResult).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [cleanMatrix.encode,candidate]
    have hm : Context Γ cleanMatrix.encode := .head _ _
    have hc : Context Γ candidate := .hypothesis (by simp [Γ])
    have hb : Context Γ suffixBijection.encode := by
      have hp : Context Γ (both (both suffixBijection.encode suffixOrder.encode) suffixClean.encode) := by
        simpa [cleanMatrix,namedBoth,Formula.not,Formula.encode,both,neg] using hm
      exact Context.conjunctionLeft (Context.conjunctionLeft hp)
    have hr : Context Γ rowResult.encode := .mp hb (.mp hc (.closed row))
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using Context.conjunctionIntro hm hr
  have hv : KDerivation (imp candidate (allCode 6 candidate)) := by
    exact candidate_vacuity 31 213 209 210 202 0 203 205 206 6 (by decide)
  have hlift := conditionalExistsCongr 6 hv hpoint
  have hclean : KDerivation (imp (equivAt 31 40).encode (existsCode 6 cleanMatrix.encode)) := by
    simpa [cleanSuffixResult,cleanMatrix,suffixBijection,suffixOrder,Formula.encode] using clean_suffix_equiv_exists
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt 31 40).encode,candidate]
  have he : Context Γ (equivAt 31 40).encode := .head _ _
  have hc : Context Γ candidate := .hypothesis (by simp [Γ])
  have hg : Context Γ (existsCode 6 cleanMatrix.encode) := .mp he (.closed hclean)
  have hp : Context Γ (existsCode 6 (namedBoth cleanMatrix rowResult).encode) :=
    .mp hg (.mp hc (.closed hlift))
  simpa [result,Formula.encode] using hp

end PASoundness.PAtoCompactCleanSuffixRowPackage
#print axioms PASoundness.PAtoCompactCleanSuffixRowPackage.package_of_row
