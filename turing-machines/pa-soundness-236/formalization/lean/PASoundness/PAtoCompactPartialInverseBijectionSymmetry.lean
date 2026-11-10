import PASoundness.PAtoCompactRestrictedSymmetry

/-! Conditional candidate symmetry from represented inverse graphs for
bijection witnesses. This weakens only the proof wrapper's graph-existence
premise; it does not establish the premise or an unguarded quotient. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseBijectionSymmetry
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoSwap
open PASoundness.PAtoCompactIsoConditionalWrapper PASoundness.PAtoCompactRestrictedInverseFirst
open PASoundness.PAtoCompactRestrictedSymmetry
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- For every represented graph satisfying the actual bijection formula,
there is a represented inverse satisfying the restricted correspondence.
This is an explicit premise, not a theorem of this module. -/
def bijectionInversePremise : Nat := allCode 6 (imp bijectionFormula.encode
  (existsCode 7 restrictedInverseMatrix.encode))

/-- Bijection-level inverse existence supplies the matrix-level premise. -/
def bijection_premise_transport : KDerivation
    (imp bijectionInversePremise (allCode 6 (imp forwardMatrix.encode
      (existsCode 7 restrictedInverseMatrix.encode)))) := by
  let B := bijectionFormula.encode
  let F := forwardMatrix.encode
  let I := existsCode 7 restrictedInverseMatrix.encode
  have hp : KDerivation (imp (imp B I) (imp F I)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [F,imp B I]
    have hf : Context Γ F := Context.head _ _
    have hi : Context Γ (imp B I) := .hypothesis (by simp [Γ])
    exact .mp (Context.conjunctionLeft hf) hi
  exact allCongr 6 hp

/-- The proposed quotient equality is symmetric under the displayed
bijection-level inverse existence premise. -/
def symmetry_of_bijection_inverses : KDerivation
    (imp bijectionInversePremise (imp equivalentFormula.encode reverseEquivalent.encode)) :=
  compose bijection_premise_transport candidate_restricted_symmetry

theorem symmetry_of_bijection_inverses_certificate :
    theoremCode (certificate symmetry_of_bijection_inverses) =
      imp bijectionInversePremise (imp equivalentFormula.encode reverseEquivalent.encode) :=
  certificate_correct symmetry_of_bijection_inverses

end PASoundness.PAtoCompactPartialInverseBijectionSymmetry

#print axioms PASoundness.PAtoCompactPartialInverseBijectionSymmetry.bijection_premise_transport
#print axioms PASoundness.PAtoCompactPartialInverseBijectionSymmetry.symmetry_of_bijection_inverses
#print axioms PASoundness.PAtoCompactPartialInverseBijectionSymmetry.symmetry_of_bijection_inverses_certificate
