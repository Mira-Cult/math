import PASoundness.PAtoCompactAdditionCleanEquivWitness
import PASoundness.PAtoCompactMultiplicationSuffixCleanEdges

/-! Construct a clean source31/suffix40 isomorphism graph from the actual
supplied equivalence, by capture-safe specialization of the existing K graph
cleaning theorem. This does not construct a multiplication row. -/
namespace PASoundness.PAtoCompactMultiplicationSuffixCleanExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionCleanEquivWitness
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The cleaned graph satisfies both original isomorphism clauses as well as
the exact endpoint-cleanliness formula used by same-row comparison. -/
def cleanSuffixResult : Formula := .ex 6
  (namedBoth (namedBoth (replace 1 40 (replace 0 31 bijectionFormula))
    (replace 1 40 (replace 0 31 orderFormula))) suffixClean)

private def oldResult : Formula := .ex 6
  (namedBoth (namedBoth (replace 1 34 (replace 0 31 bijectionFormula))
    (replace 1 34 (replace 0 31 orderFormula)))
    (.all 19 (.imp (.member 6 19) (edgePredicate 19 31 34))))
private def statement : Formula := .imp (equivAt 31 34) oldResult

/-- For the literal equivalence 31↔40, K constructs a single clean graph 6
retaining the full source/target isomorphism matrix. -/
def clean_suffix_equiv_exists : KDerivation
    (imp (equivAt 31 40).encode cleanSuffixResult.encode) := by
  have h : KDerivation statement.encode := by
    simpa [statement, oldResult, Formula.encode] using clean_equiv_witness
  have hi := universalInstance 34 40 statement (by decide) (by decide) (by decide)
  have h' := KDerivation.mp (.generalize 34 h) hi
  have he : replace 34 40 statement = .imp (equivAt 31 40) cleanSuffixResult := by decide
  rw [he] at h'
  exact h'

theorem clean_suffix_equiv_exists_certificate :
    theoremCode (certificate clean_suffix_equiv_exists) =
      imp (equivAt 31 40).encode cleanSuffixResult.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationSuffixCleanExists
#print axioms PASoundness.PAtoCompactMultiplicationSuffixCleanExists.clean_suffix_equiv_exists
#print axioms PASoundness.PAtoCompactMultiplicationSuffixCleanExists.clean_suffix_equiv_exists_certificate
