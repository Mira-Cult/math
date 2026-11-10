import PASoundness.PAtoCompactSuccTopWitness
import PASoundness.PAtoCompactGraphAdjoinPreserve

/-! An actual K top-edge and old-edge construction for the unequal-endpoint
addition-successor graph. The graph and pair adjunction witnesses are supplied;
no existence, isomorphism, or arithmetic axiom is asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorGraphTop
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccTopWitness
open PASoundness.PAtoCompactGraphAdjoinPreserve
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The supplied pair object 11 denotes the ordered pair with distinct source
and target names 31 and 32. Its graph witness is introduced at name 19. -/
def top_from_pair : KDerivation
    (imp (both (member 9 11) (pairFormula 11 31 32).encode)
      (graphFormula 9 31 32).encode) := by
  let f : Formula := namedBoth (.member 9 19) (pairFormula 19 31 32)
  have hi := exists_variable_intro 19 11 f (by decide) (by decide) (by decide)
  have hr : replace 19 11 f = namedBoth (.member 9 11) (pairFormula 11 31 32) := by decide
  rw [hr] at hi
  change KDerivation (imp (both (member 9 11) (pairFormula 11 31 32).encode)
    (graphFormula 9 31 32).encode) at hi
  exact hi

/-- Under the displayed adjunction and pair hypotheses, the very same new
graph contains the new top edge and preserves the supplied old (2,3) edge. -/
def new_top_and_old_edge : KDerivation
    (imp (adjoinCode 6 11 9 16)
      (imp (pairFormula 11 31 32).encode
        (imp (graphFormula 6 2 3).encode
          (both (graphFormula 9 31 32).encode (graphFormula 9 2 3).encode)))) := by
  let A := adjoinCode 6 11 9 16
  let P := (pairFormula 11 31 32).encode
  let O := (graphFormula 6 2 3).encode
  let Γ := [O,P,A]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have ho : Context Γ O := Context.head _ _
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 9 11) := by
    exact .mp ha (.closed new_graph_contains_pair)
  have ht : Context Γ (graphFormula 9 31 32).encode :=
    .mp (Context.conjunctionIntro hm hp) (.closed top_from_pair)
  have hold : Context Γ (graphFormula 9 2 3).encode :=
    .mp ho (.mp ha (.closed (adjoin_preserves_edge 6 11 9 16 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))
  exact Context.conjunctionIntro ht hold

theorem new_top_and_old_edge_certificate :
    theoremCode (certificate new_top_and_old_edge) =
      imp (adjoinCode 6 11 9 16)
        (imp (pairFormula 11 31 32).encode
          (imp (graphFormula 6 2 3).encode
            (both (graphFormula 9 31 32).encode (graphFormula 9 2 3).encode))) :=
  certificate_correct new_top_and_old_edge

end PASoundness.PAtoCompactAdditionSuccessorGraphTop

#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphTop.top_from_pair
#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphTop.new_top_and_old_edge
#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphTop.new_top_and_old_edge_certificate
