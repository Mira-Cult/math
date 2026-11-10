import PASoundness.PAtoCompactBijectionForwardImage

/-! A candidate row's source-point image from the literal K bijection matrix.
The represented graph is supplied; this module does not construct it, assert
row collection, or prove multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRowMapEdge
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Supplied F-bijection has source 31, target 32, and graph 6. -/
def mapBijection : Formula := replace 1 32 (replace 0 31 bijectionFormula)

private def witness (x : Nat) : Formula := namedBoth (.member 32 3)
  (namedBoth (graphFormula 6 x 3)
    (.all 4 (.imp (namedBoth (.member 32 4) (graphFormula 6 x 4)) (.equal 4 3))))
private def forwardBody : Formula := .imp (.member 31 2) (.ex 3 (witness 2))

/-- Source point 0 has an F-edge to some object, provided it lies in source
31 and the supplied F graph is a bijection between 31 and 32. The value is
bound at name 4; no output-value or graph existence is assumed implicitly. -/
def source_point_has_edge : KDerivation (imp mapBijection.encode
    (imp (member 31 0) (existsCode 4 (graphFormula 6 0 4).encode))) := by
  have hforward : KDerivation (imp mapBijection.encode (allCode 2 forwardBody.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    have h : Context [mapBijection.encode] mapBijection.encode := .head _ _
    change Context [mapBijection.encode] (both (allCode 2 forwardBody.encode) _) at h
    exact Context.conjunctionLeft h
  have hinst := universalInstance 2 0 forwardBody (by decide) (by decide) (by decide)
  have hshape : replace 2 0 forwardBody = .imp (.member 31 0) (.ex 3 (witness 0)) := by decide
  rw [hshape] at hinst
  have hproj : KDerivation (imp (witness 0).encode (graphFormula 6 0 3).encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hw : Context [(witness 0).encode] (witness 0).encode := .head _ _
    change Context [(witness 0).encode] (both (member 32 3)
      (both (graphFormula 6 0 3).encode _)) at hw
    exact Context.conjunctionLeft (Context.conjunctionRight hw)
  have hmap := existsCongr 3 hproj
  have ha := (existentialAlpha 3 4 (graphFormula 6 0 3) (by decide) (by decide) (by decide)).1
  have hashape : replace 3 4 (graphFormula 6 0 3) = graphFormula 6 0 4 := by decide
  rw [hashape] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 0, mapBijection.encode]
  have hm : Context Γ (member 31 0) := .head _ _
  have hb : Context Γ mapBijection.encode := .hypothesis (by simp [Γ])
  have hall : Context Γ (allCode 2 forwardBody.encode) := .mp hb (.closed hforward)
  have hex : Context Γ (existsCode 3 (witness 0).encode) := .mp hm (.mp hall (.closed hinst))
  exact .mp (.mp hex (.closed hmap)) (.closed ha)

theorem source_point_has_edge_certificate : theoremCode (certificate source_point_has_edge) =
    imp mapBijection.encode (imp (member 31 0) (existsCode 4 (graphFormula 6 0 4).encode)) :=
  certificate_correct source_point_has_edge
end PASoundness.PAtoCompactMultiplicationRowMapEdge
#print axioms PASoundness.PAtoCompactMultiplicationRowMapEdge.source_point_has_edge
#print axioms PASoundness.PAtoCompactMultiplicationRowMapEdge.source_point_has_edge_certificate
