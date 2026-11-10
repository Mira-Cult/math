import PASoundness.PAtoCompactMultiplicationNewOldCaseGuarded
import PASoundness.PAtoCompactProductCleanEndpointsSecond

/-! The new-row/old-graph lex case from the actual clean-old endpoint theorem.
The common object-level premise and two selected graph branches remain
explicit. This does not build the graph, prove row collection, or establish
multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationNewOldCaseClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactMultiplicationFourCaseLex
open PASoundness.PAtoCompactMultiplicationNewOldCaseGuarded
open PASoundness.PAtoCompactProductCleanEndpointsSecond
attribute [local irreducible] imp PASoundness.Cantor.pair PASoundness.Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The supplied clean old graph determines the queried old triple's major
and output memberships. No old-matrix cleanliness is inferred. -/
def old_endpoints : KDerivation (imp oldCleanActual.encode
    (imp oldSecond (both (member 30 7) (member 32 9)))) := by
  have h := second_endpoints
  have hc : PASoundness.PAtoCompactProductCleanEndpointsRelocated.oldCleanActual =
      PASoundness.PAtoCompactMultiplicationLexSharedContext.oldCleanActual := by rfl
  rw [hc] at h
  have ht : secondTriple = PASoundness.PAtoCompactMultiplicationSecondBranchSplit.tripleAt 10 :=
    PASoundness.PAtoCompactMultiplicationSecondBranchSplit.old_triple_shape
  rw [ht] at h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldSecond,oldCleanActual.encode]
  have hs : Context Γ oldSecond := .head _ _
  have hc' : Context Γ oldCleanActual.encode := .hypothesis (by simp [Γ])
  have he : Context Γ (both (member 30 7) (both (member 31 8) (member 32 9))) := by
    have hr := Context.mp hs (Context.mp hc' (.closed h))
    simpa [oldSecond,secondEndpoints,namedBoth,Formula.not,Formula.encode,both,neg] using hr
  exact Context.conjunctionIntro (Context.conjunctionLeft he)
    (Context.conjunctionRight (Context.conjunctionRight he))

/-- Both actual lex comparisons for the explicit new-row/old-graph case,
with no additional proof-data inputs. -/
def new_old_case : KDerivation
    (imp sharedPremise.encode (imp newFirst (imp oldSecond comparisons))) :=
  new_old_from_endpoints old_endpoints

theorem old_endpoints_certificate : theoremCode (certificate old_endpoints) =
    imp oldCleanActual.encode (imp oldSecond (both (member 30 7) (member 32 9))) :=
  certificate_correct _

theorem new_old_case_certificate : theoremCode (certificate new_old_case) =
    imp sharedPremise.encode (imp newFirst (imp oldSecond comparisons)) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationNewOldCaseClosed
#print axioms PASoundness.PAtoCompactMultiplicationNewOldCaseClosed.old_endpoints
#print axioms PASoundness.PAtoCompactMultiplicationNewOldCaseClosed.new_old_case
#print axioms PASoundness.PAtoCompactMultiplicationNewOldCaseClosed.old_endpoints_certificate
#print axioms PASoundness.PAtoCompactMultiplicationNewOldCaseClosed.new_old_case_certificate
