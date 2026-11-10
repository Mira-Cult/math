import PASoundness.PAtoCompactProductMatchInsideImage
import PASoundness.PAtoCompactScopedActiveReplace

/-! The new-edge case of the inside-source product-match extension. A
competitor match at the same source has the selected target by the concrete
pointwise functionality proof; equality replacement then transports the
selected graph edge. No partial graph or coverage theorem is asserted. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchEndpointEdge

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchRelation PASoundness.PAtoCompactProductMatchPartialBase
open PASoundness.PAtoCompactProductMatchInsideImage

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def functionalFrame : Formula := .imp path (.imp (replace 35 55 path) (.equal 55 35))
def relocatedFrame : Formula := replace 55 57 (replace 32 74 functionalFrame)

theorem relocated_frame_shape : relocatedFrame = .imp selectedPath
    (.imp (replace 35 57 selectedPath) (.equal 57 35)) := by decide

/-- If query source 56 equals the selected source 74, any matching target 57
is equal to selected target 35. Both literal path witnesses are required. -/
def endpoint_unique : KDerivation (imp (equal 56 74)
    (imp selectedPath.encode (imp matchAt.encode (equal 57 35)))) := by
  have h0 : KDerivation functionalFrame.encode := by
    simpa [functionalFrame, Formula.encode] using path_functional
  have h1 := replace_derivation 32 74 functionalFrame (by decide) (by decide) h0
  have h2 := replace_derivation 55 57 (replace 32 74 functionalFrame)
    (by decide) (by decide) h1
  change KDerivation relocatedFrame.encode at h2
  rw [relocated_frame_shape] at h2
  have he := (equalityReplace 56 74 matchAt (by decide) (by decide)).1
  have hshape : replace 56 74 matchAt = replace 35 57 selectedPath := by decide
  rw [hshape] at he
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [matchAt.encode,selectedPath.encode,equal 56 74]
  have hm : Context Γ matchAt.encode := .head _ _
  have hp : Context Γ selectedPath.encode := .hypothesis (by simp [Γ])
  have hx : Context Γ (equal 56 74) := .hypothesis (by simp [Γ])
  have hpath : Context Γ (replace 35 57 selectedPath).encode := .mp hm (.mp hx (.closed he))
  have hf := Context.mp hpath (Context.mp hp (.closed h2))
  simpa [Formula.encode] using hf

/-- The selected graph edge also covers any matching query at that same
source endpoint, even when the displayed labels denote equal objects. -/
def endpoint_edge : KDerivation (imp (equal 56 74)
    (imp selectedPath.encode (imp (graphFormula 17 74 35).encode
      (imp matchAt.encode (graphFormula 17 56 57).encode)))) := by
  have hs := (equalityReplace 74 56 (graphFormula 17 74 35) (by decide) (by decide)).1
  have hss : replace 74 56 (graphFormula 17 74 35) = graphFormula 17 56 35 := by decide
  rw [hss] at hs
  have ht := (equalityReplace 35 57 (graphFormula 17 56 35) (by decide) (by decide)).1
  have hst : replace 35 57 (graphFormula 17 56 35) = graphFormula 17 56 57 := by decide
  rw [hst] at ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [matchAt.encode,(graphFormula 17 74 35).encode,selectedPath.encode,equal 56 74]
  have hm : Context Γ matchAt.encode := .head _ _
  have hg : Context Γ (graphFormula 17 74 35).encode := .hypothesis (by simp [Γ])
  have hp : Context Γ selectedPath.encode := .hypothesis (by simp [Γ])
  have hx : Context Γ (equal 56 74) := .hypothesis (by simp [Γ])
  have hy : Context Γ (equal 57 35) := .mp hm (.mp hp (.mp hx (.closed endpoint_unique)))
  have hs' : Context Γ (equal 74 56) := Context.eqSymm hx
  have ht' : Context Γ (equal 35 57) := Context.eqSymm hy
  have hedge := Context.mp hg (Context.mp hs' (.closed hs))
  exact .mp hedge (.mp ht' (.closed ht))

theorem endpoint_edge_certificate : theoremCode (certificate endpoint_edge) =
    imp (equal 56 74) (imp selectedPath.encode (imp (graphFormula 17 74 35).encode
      (imp matchAt.encode (graphFormula 17 56 57).encode))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchEndpointEdge

#print axioms PASoundness.PAtoCompactProductMatchEndpointEdge.endpoint_unique
#print axioms PASoundness.PAtoCompactProductMatchEndpointEdge.endpoint_edge
#print axioms PASoundness.PAtoCompactProductMatchEndpointEdge.endpoint_edge_certificate
