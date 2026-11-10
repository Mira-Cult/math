import PASoundness.PAtoCompactConditionalTransitivityWitnessInterface

/-! A concrete fresh-name graph-selection premise for conditional quotient
transitivity. The premise is retained; no composition graph is constructed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivitySelection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivityMatrix
open PASoundness.PAtoCompactConditionalTransitivityWitnessInterface
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def source40 : Formula := replace 6 40 sourceMatrix
private def second41 : Formula := replace 7 41 secondMatrix
private def composition40_41 : Formula := replace 7 41 (replace 6 40 composition)
private def selectionBody : Formula := source40.imp
  (second41.imp (.ex 9 composition40_41))

/-- For each pair of represented source isomorphisms, an explicitly
represented restricted composite graph exists. Fresh graph labels 40 and 41
avoid capture when this condition is instantiated at graph names 6 and 7. -/
def graphSelection : Formula := .all 40 (.all 41 selectionBody)

theorem graphSelection_fresh6 : 6 ∉ graphSelection.names := by decide
theorem graphSelection_fresh7 : 7 ∉ graphSelection.names := by decide

private def selectionAfter40 : Formula := sourceMatrix.imp
  (second41.imp (.ex 9 (replace 7 41 composition)))

private theorem after40_syntax : replace 40 6 (.all 41 selectionBody) =
    .all 41 selectionAfter40 := by decide
private theorem after41_syntax : replace 41 7 selectionAfter40 =
    sourceMatrix.imp (secondMatrix.imp (.ex 9 composition)) := by decide

/-- The exact condition yields its fixed-name graph-selection instance by
literal K universal instantiation, without assuming it is true. -/
def selection_instance : KDerivation (imp graphSelection.encode
    (imp sourceMatrix.encode (imp secondMatrix.encode (existsCode 9 composition.encode)))) := by
  have h40 := universalInstance 40 6 (.all 41 selectionBody)
    (by decide) (by decide) (by decide)
  rw [after40_syntax] at h40
  have h41 := universalInstance 41 7 selectionAfter40
    (by decide) (by decide) (by decide)
  rw [after41_syntax] at h41
  simpa only [graphSelection, Formula.encode] using compose h40 h41

/-- Given the explicit graph-selection condition, K derives the exact
conditional transitivity instance E(0,1) → E(1,8) → E(0,8). -/
def conditional_transitivity : KDerivation (imp graphSelection.encode
    (imp PAtoCompactOrderIsomorphism.equivalentFormula.encode
      (imp secondEquivalent.encode targetEquivalent.encode))) :=
  conditional_graph_transport graphSelection graphSelection_fresh6 graphSelection_fresh7 selection_instance

theorem conditional_transitivity_certificate :
    theoremCode (certificate conditional_transitivity) = imp graphSelection.encode
      (imp PAtoCompactOrderIsomorphism.equivalentFormula.encode
        (imp secondEquivalent.encode targetEquivalent.encode)) :=
  certificate_correct conditional_transitivity

end PASoundness.PAtoCompactConditionalTransitivitySelection

#print axioms PASoundness.PAtoCompactConditionalTransitivitySelection.selection_instance
#print axioms PASoundness.PAtoCompactConditionalTransitivitySelection.conditional_transitivity
#print axioms PASoundness.PAtoCompactConditionalTransitivitySelection.conditional_transitivity_certificate
