import PASoundness.PAtoCompactSuccessorCancellationPrepared
import PASoundness.PAtoCompactEquivalentEndpointAlias

/-! A finite K successor-restriction derivation whose old endpoints are
expressed by explicit, capture-safe equality-guarded aliases. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccessorCancellationAliased
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactEquivalentAliasInstantiation
open PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.PAtoCompactSuccessorCancellationPrepared
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under the displayed literal successor and transitivity hypotheses, an
original isomorphism at 0,1 yields the equality-guarded alias instance of
that same canonical formula at 2,5. This derivation does not assert that raw
uniform replacement through its binders is capture safe. -/
def successor_cancellation_aliased : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12)
        (imp equivalentFormula.encode (guarded originalAliases).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equivalentFormula.encode, transitiveCode 5 11 12,
    successorCode 5 1 10, successorCode 2 0 9]
  have he : Context Γ equivalentFormula.encode := .head _ _
  have ht : Context Γ (transitiveCode 5 11 12) := .hypothesis (by simp [Γ])
  have hy : Context Γ (successorCode 5 1 10) := .hypothesis (by simp [Γ])
  have hx : Context Γ (successorCode 2 0 9) := .hypothesis (by simp [Γ])
  exact .mp (.mp he (.mp ht (.mp hy (.mp hx (.closed successor_cancellation_prepared)))))
    (.closed PASoundness.PAtoCompactEquivalentEndpointAlias.backward)

theorem successor_cancellation_aliased_certificate :
    theoremCode (certificate successor_cancellation_aliased) =
      imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
        (imp (transitiveCode 5 11 12)
          (imp equivalentFormula.encode (guarded originalAliases).encode))) :=
  certificate_correct successor_cancellation_aliased

end PASoundness.PAtoCompactSuccessorCancellationAliased

#print axioms PASoundness.PAtoCompactSuccessorCancellationAliased.successor_cancellation_aliased
#print axioms PASoundness.PAtoCompactSuccessorCancellationAliased.successor_cancellation_aliased_certificate
