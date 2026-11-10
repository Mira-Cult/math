import PASoundness.PAtoCompactSelectedCutRenamedGuard
import PASoundness.PAtoCompactStagedEquivalenceAligned

/-! Extract the whole-output isomorphism's actual graph at the label used by
selected-cut and suffix transport. No selected cut or suffix is constructed. -/
namespace PASoundness.PAtoCompactSelectedCutOutputMatrix
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactStagedEquivalenceAlpha
open PASoundness.PAtoCompactStagedEquivalenceAligned PASoundness.PAtoCompactSelectedCutRenamedGuard
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldBijection : Formula := replace 1 8 (replace 0 32 bijectionFormula)
def oldOrder : Formula := replace 1 8 (replace 0 32 orderFormula)
def oldMatrix : Formula := namedBoth oldBijection oldOrder
def graphMatrix : Formula := namedBoth targetBijection targetOrder
def graphWitness : Formula := .ex 60 graphMatrix

private theorem source_shape : rawStaged 32 8 = .ex 6 oldMatrix := by decide
private theorem graph_shape : replace 6 60 oldMatrix = graphMatrix := by decide

/-- The allocated isomorphism of source 32 and target 8 gives its actual
bijective order graph, with the graph binder alpha-renamed to 60. Both
matrix fields refer to the same graph. No candidate or distinct-value
assumptions are added. -/
def graph_from_output_equivalence : KDerivation
    (imp (equivAt 100 32 8).encode graphWitness.encode) := by
  have hraw := allocated_to_staged 32 8 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [source_shape] at hraw
  have halpha := (existentialAlpha 6 60 oldMatrix (by decide) (by decide) (by decide)).1
  rw [graph_shape] at halpha
  have h := compose hraw halpha
  simpa only [graphWitness,Formula.encode] using h

theorem graph_from_output_equivalence_certificate :
    theoremCode (certificate graph_from_output_equivalence) =
      imp (equivAt 100 32 8).encode graphWitness.encode :=
  certificate_correct graph_from_output_equivalence
end PASoundness.PAtoCompactSelectedCutOutputMatrix

#print axioms PASoundness.PAtoCompactSelectedCutOutputMatrix.graph_from_output_equivalence
#print axioms PASoundness.PAtoCompactSelectedCutOutputMatrix.graph_from_output_equivalence_certificate
