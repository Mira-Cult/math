import PASoundness.PAtoCompactConditionalTransitivityMatrix
import PASoundness.PAtoCompactConditionalTransitivityExists
import PASoundness.PAtoCompactConditionalTransitivityBijection

/-! Graph-witness packaging for the exact quotient candidate.
The graph-selection premise and its K instantiation proof remain explicit;
the bijection and order transfers are proved. No composition graph is
constructed here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityWitnessInterface
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivityMatrix
open PASoundness.PAtoCompactConditionalTransitivityExists
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The literal second and target candidates, with input names changed
before alpha-renaming their graph witnesses. -/
def secondEquivalent : Formula := replace 0 1 (replace 1 8 equivalentFormula)
def targetEquivalent : Formula := replace 1 8 equivalentFormula
private def secondBefore : Formula := replace 0 1 (replace 1 8 sourceMatrix)
private def targetBefore : Formula := replace 1 8 sourceMatrix

private theorem source_syntax : equivalentFormula.encode =
    existsCode 6 sourceMatrix.encode := rfl
private theorem second_syntax : secondEquivalent.encode =
    existsCode 6 secondBefore.encode := rfl
private theorem target_syntax : targetEquivalent.encode =
    existsCode 6 targetBefore.encode := rfl
private theorem second_renamed : replace 6 7 secondBefore = secondMatrix := rfl
private theorem target_renamed : replace 6 9 targetBefore = targetMatrix := rfl

/-- Conditional composition for the exact graph-existential candidates.
`Q` is an explicit graph-selection condition fresh at the two original graph
witness names. `select` is its explicit K instantiation proof. Both the matrix
order and bijection transfers are actual K proofs. No graph existence or
selection premise is asserted here. -/
def conditional_graph_transport (Q : Formula) (hQ6 : 6 ∉ Q.names) (hQ7 : 7 ∉ Q.names)
    (select : KDerivation (imp Q.encode (imp sourceMatrix.encode
      (imp secondMatrix.encode (existsCode 9 composition.encode))))) :
    KDerivation (imp Q.encode (imp equivalentFormula.encode
      (imp secondEquivalent.encode targetEquivalent.encode))) := by
  have htransport := transport_two_exists 6 7 9 sourceMatrix secondMatrix composition
    targetMatrix Q (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hQ6 hQ7 (by decide) (by decide)
    select (matrix_of_bijection PAtoCompactConditionalTransitivityBijection.bijection_transfer)
  have hsecond := (existentialAlpha 6 7 secondBefore
    (by decide) (by decide) (by decide)).1
  have hsecond' : KDerivation (imp (existsCode 6 secondBefore.encode)
      (existsCode 7 secondMatrix.encode)) := by
    simpa only [second_renamed, Formula.encode] using hsecond
  have htarget := (existentialAlpha 6 9 targetBefore
    (by decide) (by decide) (by decide)).2
  have htarget' : KDerivation (imp (existsCode 9 targetMatrix.encode)
      (existsCode 6 targetBefore.encode)) := by
    simpa only [target_renamed, Formula.encode] using htarget
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondEquivalent.encode, equivalentFormula.encode, Q.encode]
  have hq : Context Γ Q.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ (existsCode 6 sourceMatrix.encode) := by
    simpa only [source_syntax] using
      (Context.hypothesis (by simp [Γ]) : Context Γ equivalentFormula.encode)
  have hg6 : Context Γ (existsCode 6 secondBefore.encode) := by
    rw [← second_syntax]
    exact Context.head _ _
  have hg7 : Context Γ (existsCode 7 secondMatrix.encode) := .mp hg6 (.closed hsecond')
  have hh9 : Context Γ (existsCode 9 targetMatrix.encode) :=
    .mp hg7 (.mp hf (.mp hq (.closed htransport)))
  have hh6 : Context Γ (existsCode 6 targetBefore.encode) := .mp hh9 (.closed htarget')
  simpa only [target_syntax] using hh6

theorem conditional_graph_transport_certificate (Q : Formula)
    (hQ6 : 6 ∉ Q.names) (hQ7 : 7 ∉ Q.names)
    (select : KDerivation (imp Q.encode (imp sourceMatrix.encode
      (imp secondMatrix.encode (existsCode 9 composition.encode))))) :
    theoremCode (certificate (conditional_graph_transport Q hQ6 hQ7 select)) =
      imp Q.encode (imp equivalentFormula.encode
        (imp secondEquivalent.encode targetEquivalent.encode)) :=
  certificate_correct (conditional_graph_transport Q hQ6 hQ7 select)

end PASoundness.PAtoCompactConditionalTransitivityWitnessInterface

#print axioms PASoundness.PAtoCompactConditionalTransitivityWitnessInterface.conditional_graph_transport
#print axioms PASoundness.PAtoCompactConditionalTransitivityWitnessInterface.conditional_graph_transport_certificate
