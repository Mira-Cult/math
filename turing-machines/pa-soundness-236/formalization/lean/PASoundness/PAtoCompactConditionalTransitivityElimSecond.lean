import PASoundness.PAtoCompactConditionalTransitivityPoint

/-! The second guarded composite edge exposes a separately named middle
witness. Composition is supplied explicitly and remains restricted to the
two endpoint domains; no graph existence or quotient transitivity is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityElimSecond
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def secondBody10 : Formula := namedBoth (.member 1 10)
  (namedBoth (graphFormula 6 4 10) (graphFormula 7 10 5))
def secondBody11 : Formula := namedBoth (.member 1 11)
  (namedBoth (graphFormula 6 4 11) (graphFormula 7 11 5))
def secondPath10 : Formula := .ex 10 secondBody10
def secondPath : Formula := .ex 11 secondBody11
def secondEdge : Formula := graphFormula 9 4 5
def secondEndpoints : Formula := namedBoth (.member 0 4) (.member 8 5)

private theorem first_replacement : replace 2 4 (.all 3 point) =
    .all 3 (replace 2 4 point) := by decide

private theorem second_replacement : replace 3 5 (replace 2 4 point) =
    .imp secondEndpoints (namedBoth (.imp secondEdge secondPath10)
      (.imp secondPath10 secondEdge)) := by decide

private theorem body_rename : replace 10 11 secondBody10 = secondBody11 := by decide

/-- Specialize the supplied composition at endpoint names 4 and 5, then
alpha-rename its existential middle witness from 10 to the fresh name 11. -/
def second_edge_to_path : KDerivation (imp composition.encode
    (imp (member 0 4) (imp (member 8 5)
      (imp secondEdge.encode secondPath.encode)))) := by
  let point' := (.imp secondEndpoints (namedBoth (.imp secondEdge secondPath10)
    (.imp secondPath10 secondEdge)) : Formula)
  have h2 := universalInstance 2 4 (.all 3 point) (by decide) (by decide) (by decide)
  rw [first_replacement] at h2
  have h3 := universalInstance 3 5 (replace 2 4 point) (by decide) (by decide) (by decide)
  rw [second_replacement] at h3
  have hpoint : KDerivation (imp composition.encode point'.encode) := compose h2 h3
  have halpha := (existentialAlpha 10 11 secondBody10 (by decide) (by decide) (by decide)).1
  rw [body_rename] at halpha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondEdge.encode, member 8 5, member 0 4, composition.encode]
  have hc : Context Γ composition.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 0 4) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 8 5) := .hypothesis (by simp [Γ])
  have he : Context Γ secondEdge.encode := Context.head _ _
  have hp : Context Γ point'.encode := .mp hc (.closed hpoint)
  have hguard : Context Γ secondEndpoints.encode := Context.conjunctionIntro ha hb
  have hclauses : Context Γ (namedBoth (.imp secondEdge secondPath10)
      (.imp secondPath10 secondEdge)).encode := .mp hguard hp
  have hforward : Context Γ (imp secondEdge.encode secondPath10.encode) :=
    Context.conjunctionLeft hclauses
  have hpath : Context Γ (existsCode 10 secondBody10.encode) := by
    simpa only [secondPath10, Formula.encode] using (.mp he hforward)
  exact .mp hpath (.closed halpha)

/-- Eliminate the second edge's middle witness into a target that is fresh
at 11. The witness-specific proof is an explicit input. -/
def second_edge_elim (target : Formula) (fresh : 11 ∉ target.names)
    (step : KDerivation (imp secondBody11.encode target.encode)) : KDerivation
    (imp composition.encode (imp (member 0 4) (imp (member 8 5)
      (imp secondEdge.encode target.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondEdge.encode, member 8 5, member 0 4, composition.encode]
  have hc : Context Γ composition.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 0 4) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 8 5) := .hypothesis (by simp [Γ])
  have he : Context Γ secondEdge.encode := Context.head _ _
  have hp : Context Γ secondPath.encode :=
    .mp he (.mp hb (.mp ha (.mp hc (.closed second_edge_to_path))))
  have hex : Context Γ (existsCode 11 secondBody11.encode) := by
    simpa only [secondPath, Formula.encode] using hp
  exact Context.existsElim (target.vacuity 11 fresh)
    (.closed (.generalize 11 step)) hex

theorem second_edge_to_path_certificate : theoremCode (certificate second_edge_to_path) =
    imp composition.encode (imp (member 0 4) (imp (member 8 5)
      (imp secondEdge.encode secondPath.encode))) := certificate_correct second_edge_to_path

theorem second_edge_elim_certificate (target : Formula) (fresh : 11 ∉ target.names)
    (step : KDerivation (imp secondBody11.encode target.encode)) :
    theoremCode (certificate (second_edge_elim target fresh step)) =
      imp composition.encode (imp (member 0 4) (imp (member 8 5)
        (imp secondEdge.encode target.encode))) := certificate_correct (second_edge_elim target fresh step)

end PASoundness.PAtoCompactConditionalTransitivityElimSecond

#print axioms PASoundness.PAtoCompactConditionalTransitivityElimSecond.second_edge_to_path
#print axioms PASoundness.PAtoCompactConditionalTransitivityElimSecond.second_edge_elim
#print axioms PASoundness.PAtoCompactConditionalTransitivityElimSecond.second_edge_elim_certificate
