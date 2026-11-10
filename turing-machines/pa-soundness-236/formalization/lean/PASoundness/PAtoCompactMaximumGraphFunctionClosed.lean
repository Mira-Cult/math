import PASoundness.PAtoCompactBijectionPointwiseUnique

/-! The equality-input case of maximum alignment, derived from the actual
bijection clause and its guarded graph edges. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMaximumGraphFunctionClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactBijectionPointwiseUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under the exact bijection clause, source member 2, codomain members 3
and 5, and displayed graph edges 2→3 and 7→5, equality 7=2 implies 3=5.
The concrete names avoid graph binders; the denoted objects may coincide.
No graph, isomorphism witness or successor relation is constructed here. -/
def equal_inputs_force_equal_images : KDerivation
    (imp bijectionFormula.encode (imp (member 0 2) (imp (member 1 3)
      (imp (graphFormula 6 2 3).encode (imp (member 1 5)
        (imp (graphFormula 6 7 5).encode (imp (equal 7 2) (equal 3 5)))))))) := by
  let G : Formula := graphFormula 6 7 5
  have hreplace : KDerivation (imp (equal 7 2)
      (imp G.encode (graphFormula 6 2 5).encode)) := by
    have h := (CompactNamed.equalityReplace 7 2 G (by decide) (by decide)).1
    have he : CompactNamed.replace 7 2 G = graphFormula 6 2 5 := by decide
    simpa only [he] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 7 2,G.encode,member 1 5,(graphFormula 6 2 3).encode,
    member 1 3,member 0 2,bijectionFormula.encode]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hsrc : Context Γ (member 0 2) := .hypothesis (by simp [Γ])
  have hm3 : Context Γ (member 1 3) := .hypothesis (by simp [Γ])
  have hg3 : Context Γ (graphFormula 6 2 3).encode := .hypothesis (by simp [Γ])
  have hm5 : Context Γ (member 1 5) := .hypothesis (by simp [Γ])
  have hg : Context Γ G.encode := .hypothesis (by simp [Γ])
  have he : Context Γ (equal 7 2) := .head _ _
  have hg5 : Context Γ (graphFormula 6 2 5).encode := .mp hg (.mp he (.closed hreplace))
  exact .mp hg5 (.mp hm5 (.mp hg3 (.mp hm3 (.mp hsrc (.mp hb (.closed pointwise_unique))))))

theorem equal_inputs_force_equal_images_certificate :
    theoremCode (certificate equal_inputs_force_equal_images) =
      imp bijectionFormula.encode (imp (member 0 2) (imp (member 1 3)
        (imp (graphFormula 6 2 3).encode (imp (member 1 5)
          (imp (graphFormula 6 7 5).encode (imp (equal 7 2) (equal 3 5))))))) :=
  certificate_correct equal_inputs_force_equal_images

end PASoundness.PAtoCompactMaximumGraphFunctionClosed

#print axioms PASoundness.PAtoCompactMaximumGraphFunctionClosed.equal_inputs_force_equal_images
#print axioms PASoundness.PAtoCompactMaximumGraphFunctionClosed.equal_inputs_force_equal_images_certificate
