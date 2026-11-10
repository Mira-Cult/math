import PASoundness.PAtoCompactSeededSpanOrderSplit

/-! Introduce either a seed edge or a common-source path into an actual seeded
span graph under its explicit endpoint guards. These pointwise K proofs are
coverage ingredients; they do not construct either kind of witness. -/
namespace PASoundness.PAtoCompactSeededSpanEdgeIntro

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactCommonSourceSpanBase
open PASoundness.PAtoCompactSeededSpanBase PASoundness.PAtoCompactSeededSpanOrderSplit

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private theorem span_shape : seededSpan = .all 2 (.all 3 orderPoint) := by rfl
private def point_from_span : KDerivation (imp seededSpan.encode orderPoint.encode) := by
  have h2 := allSpecialize 2 (.all 3 orderPoint) (by decide)
  have h3 := allSpecialize 3 orderPoint (by decide)
  simpa only [span_shape,Formula.encode] using compose h2 h3

/-- An actual seed edge is an output edge at the guarded whole endpoints. -/
def seed_edge_intro : KDerivation (imp seededSpan.encode
    (imp (both (member 0 2) (member 8 3))
      (imp (graphFormula 14 2 3).encode (graphFormula 9 2 3).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 14 2 3).encode,both (member 0 2) (member 8 3),seededSpan.encode]
  have he : Context Γ (graphFormula 14 2 3).encode := .head _ _
  have hm : Context Γ (both (member 0 2) (member 8 3)) := .hypothesis (by simp [Γ])
  have hi : Context Γ seededSpan.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ orderPoint.encode := .mp hi (.closed point_from_span)
  have hc : Context Γ (both (imp (graphFormula 9 2 3).encode
      (either (graphFormula 14 2 3).encode spanPath.encode))
    (imp (either (graphFormula 14 2 3).encode spanPath.encode) (graphFormula 9 2 3).encode)) := .mp hm hp
  have hu : Context Γ (either (graphFormula 14 2 3).encode spanPath.encode) := Context.disjunctionLeft he
  exact .mp hu (Context.conjunctionRight hc)

/-- An actual common-source path is an output edge at the guarded whole endpoints. -/
def path_edge_intro : KDerivation (imp seededSpan.encode
    (imp (both (member 0 2) (member 8 3))
      (imp spanPath.encode (graphFormula 9 2 3).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [spanPath.encode,both (member 0 2) (member 8 3),seededSpan.encode]
  have he : Context Γ spanPath.encode := .head _ _
  have hm : Context Γ (both (member 0 2) (member 8 3)) := .hypothesis (by simp [Γ])
  have hi : Context Γ seededSpan.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ orderPoint.encode := .mp hi (.closed point_from_span)
  have hc : Context Γ (both (imp (graphFormula 9 2 3).encode
      (either (graphFormula 14 2 3).encode spanPath.encode))
    (imp (either (graphFormula 14 2 3).encode spanPath.encode) (graphFormula 9 2 3).encode)) := .mp hm hp
  have hu : Context Γ (either (graphFormula 14 2 3).encode spanPath.encode) := Context.disjunctionRight he
  exact .mp hu (Context.conjunctionRight hc)

theorem seed_edge_intro_certificate : theoremCode (certificate seed_edge_intro) =
    imp seededSpan.encode (imp (both (member 0 2) (member 8 3))
      (imp (graphFormula 14 2 3).encode (graphFormula 9 2 3).encode)) := certificate_correct seed_edge_intro
theorem path_edge_intro_certificate : theoremCode (certificate path_edge_intro) =
    imp seededSpan.encode (imp (both (member 0 2) (member 8 3))
      (imp spanPath.encode (graphFormula 9 2 3).encode)) := certificate_correct path_edge_intro

end PASoundness.PAtoCompactSeededSpanEdgeIntro

#print axioms PASoundness.PAtoCompactSeededSpanEdgeIntro.seed_edge_intro
#print axioms PASoundness.PAtoCompactSeededSpanEdgeIntro.path_edge_intro
#print axioms PASoundness.PAtoCompactSeededSpanEdgeIntro.seed_edge_intro_certificate
#print axioms PASoundness.PAtoCompactSeededSpanEdgeIntro.path_edge_intro_certificate
