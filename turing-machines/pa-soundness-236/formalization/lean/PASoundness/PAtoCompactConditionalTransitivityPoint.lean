import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.CompactQuantifiers

/-! Pointwise introduction and elimination for an explicitly supplied
domain-restricted composite graph. This neither constructs the graph nor
asserts transitivity of the proposed quotient equivalence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A path with middle witness 10, through graphs 6 and 7 and domain 1. -/
def pathBody : Formula := namedBoth (.member 1 10)
  (namedBoth (graphFormula 6 2 10) (graphFormula 7 10 3))

def path : Formula := .ex 10 pathBody
def edge : Formula := graphFormula 9 2 3
def endpoints : Formula := namedBoth (.member 0 2) (.member 8 3)
def point : Formula := .imp endpoints (namedBoth (.imp edge path) (.imp path edge))

/-- The supplied graph 9 is exactly the relational composition on endpoints
from 0 and 8; the intermediate element is required to belong to 1. -/
def composition : Formula := .all 2 (.all 3 point)

/-- The two universally quantified endpoint names specialize to themselves;
internal graph binders and the path witness remain capture-safe. -/
def composition_point : KDerivation (imp composition.encode point.encode) := by
  have h2 := CompactNamed.allSpecialize 2 (.all 3 point) (by decide)
  have h3 := CompactNamed.allSpecialize 3 point (by decide)
  exact CompactDerivations.compose h2 h3

/-- Under the endpoint guard, a supplied composite edge exposes a path with
an existential intermediate witness. -/
def edge_to_path : KDerivation (imp composition.encode
    (imp (member 0 2) (imp (member 8 3)
      (imp edge.encode path.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [edge.encode, member 8 3, member 0 2, composition.encode]
  have hc : Context Γ composition.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 0 2) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 8 3) := .hypothesis (by simp [Γ])
  have he : Context Γ edge.encode := Context.head _ _
  have hp : Context Γ point.encode := .mp hc (.closed composition_point)
  have hguard : Context Γ endpoints.encode := Context.conjunctionIntro ha hb
  have hclauses : Context Γ (namedBoth (.imp edge path) (.imp path edge)).encode :=
    .mp hguard hp
  have hforward : Context Γ (imp edge.encode path.encode) := Context.conjunctionLeft hclauses
  exact .mp he hforward

/-- The same concrete middle witness forms an existential path and therefore
the supplied composite edge; no fresh or uniform witness is postulated. -/
def chain_to_edge : KDerivation (imp composition.encode
    (imp (member 0 2) (imp (member 8 3) (imp (member 1 10)
      (imp (graphFormula 6 2 10).encode (imp (graphFormula 7 10 3).encode edge.encode)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let F := (graphFormula 6 2 10).encode
  let G := (graphFormula 7 10 3).encode
  let Γ := [G,F,member 1 10,member 8 3,member 0 2,composition.encode]
  have hc : Context Γ composition.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 0 2) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 8 3) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 10) := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hg : Context Γ G := Context.head _ _
  have hbody : Context Γ pathBody.encode := Context.conjunctionIntro hm (Context.conjunctionIntro hf hg)
  have hp : Context Γ path.encode := .mp hbody (.closed (CompactNamed.existsIntroduce 10 pathBody (by decide)))
  have hpoint : Context Γ point.encode := .mp hc (.closed composition_point)
  have hguard : Context Γ endpoints.encode := Context.conjunctionIntro ha hb
  have hclauses : Context Γ (namedBoth (.imp edge path) (.imp path edge)).encode :=
    .mp hguard hpoint
  have hbackward : Context Γ (imp path.encode edge.encode) := Context.conjunctionRight hclauses
  exact .mp hp hbackward

theorem edge_to_path_certificate : theoremCode (certificate edge_to_path) =
    imp composition.encode (imp (member 0 2) (imp (member 8 3)
      (imp edge.encode path.encode))) := certificate_correct edge_to_path

theorem chain_to_edge_certificate : theoremCode (certificate chain_to_edge) =
    imp composition.encode (imp (member 0 2) (imp (member 8 3) (imp (member 1 10)
      (imp (graphFormula 6 2 10).encode (imp (graphFormula 7 10 3).encode edge.encode))))) :=
  certificate_correct chain_to_edge

end PASoundness.PAtoCompactConditionalTransitivityPoint

#print axioms PASoundness.PAtoCompactConditionalTransitivityPoint.edge_to_path
#print axioms PASoundness.PAtoCompactConditionalTransitivityPoint.chain_to_edge
#print axioms PASoundness.PAtoCompactConditionalTransitivityPoint.chain_to_edge_certificate
