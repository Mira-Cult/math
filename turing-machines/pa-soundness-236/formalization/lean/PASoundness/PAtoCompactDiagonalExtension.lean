import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactAdjunction
import PASoundness.PAtoCompactTransitiveWitness

/-! A bounded syntactic ingredient for extending a supplied diagonal graph.
The point, pair graph, and graph membership are explicit hypotheses. This does
not construct an identity graph, prove no-garbage preservation, or provide a
collection principle. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalExtension
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactTransitiveWitness

/-- Equality of the candidate argument and the old endpoint transports the
supplied diagonal Kuratowski predicate to that argument. Labels 0,2,8 avoid
all actual internal binders 20--22. -/
def transport_diagonal_pair : KDerivation
    (imp (equal 0 2) (imp (pairFormula 8 0 0).encode (pairFormula 8 2 2).encode)) := by
  have h := (CompactNamed.equalityReplace 0 2 (pairFormula 8 0 0)
    (by decide) (by decide)).1
  have he : CompactNamed.replace 0 2 (pairFormula 8 0 0) = pairFormula 8 2 2 := by decide
  rw [he] at h
  exact h

/-- A supplied member p of g with its exact pair predicate provides the
corresponding graph edge. The witness-name substitution avoids binders 20--22. -/
def graph_edge_intro : KDerivation
    (imp (both (member 7 8) (pairFormula 8 2 2).encode) (graphFormula 7 2 2).encode) := by
  let f : Formula := ((Formula.member 7 19).imp (pairFormula 19 2 2).not).not
  have h := exists_variable_intro 19 8 f (by decide) (by decide) (by decide)
  have hf : (CompactNamed.replace 19 8 f).encode =
      both (member 7 8) (pairFormula 8 2 2).encode := by
    have hf' : CompactNamed.replace 19 8 f =
        ((Formula.member 7 8).imp (pairFormula 8 2 2).not).not := by decide
    rw [hf']
    rfl
  have hg : existsCode 19 f.encode = (graphFormula 7 2 2).encode := by
    rfl
  rw [hf,hg] at h
  exact h

/-- The newly adjoined diagonal pair supplies the edge for any equal endpoint.
No extensionality, pair uniqueness, or semantic-model theorem is used. -/
def diagonal_new_edge : KDerivation
    (imp (member 7 8) (imp (pairFormula 8 0 0).encode
      (imp (equal 0 2) (graphFormula 7 2 2).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 0 2,(pairFormula 8 0 0).encode,member 7 8]
  have he : Context Γ (equal 0 2) := .hypothesis (by simp [Γ])
  have hp : Context Γ (pairFormula 8 0 0).encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 7 8) := .hypothesis (by simp [Γ])
  have hp' : Context Γ (pairFormula 8 2 2).encode := .mp hp (.mp he (.closed transport_diagonal_pair))
  exact .mp (Context.conjunctionIntro hm hp') (.closed graph_edge_intro)

theorem diagonal_new_edge_certificate :
    theoremCode (certificate diagonal_new_edge) =
      imp (member 7 8) (imp (pairFormula 8 0 0).encode
        (imp (equal 0 2) (graphFormula 7 2 2).encode)) :=
  certificate_correct diagonal_new_edge

/-- An old edge remains an edge if every old graph entry belongs to the new
graph. The explicit inclusion is already quantified at the graph witness name. -/
def diagonal_old_edge : KDerivation
    (imp (allCode 19 (imp (member 6 19) (member 7 19)))
      (imp (graphFormula 6 2 2).encode (graphFormula 7 2 2).encode)) := by
  let M := member 6 19
  let N := member 7 19
  let P := (pairFormula 19 2 2).encode
  let H := allCode 19 (imp M N)
  let A := both M P
  let B := both N P
  have hlocal : KDerivation (imp (imp M N) (imp A B)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A,imp M N]
    have ha : Context Γ A := .hypothesis (by simp [Γ])
    have hi : Context Γ (imp M N) := .hypothesis (by simp [Γ])
    exact Context.conjunctionIntro (.mp (Context.conjunctionLeft ha) hi) (Context.conjunctionRight ha)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 2 2).encode,H]
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hg : Context Γ (graphFormula 6 2 2).encode := .hypothesis (by simp [Γ])
  have hall : Context Γ (allCode 19 (imp A B)) := Context.allMP hh (.closed (.generalize 19 hlocal))
  have hex : Context Γ (existsCode 19 A) := hg
  have hnew : Context Γ (existsCode 19 B) := exists_map_context hall hex
  exact hnew

theorem diagonal_old_edge_certificate :
    theoremCode (certificate diagonal_old_edge) =
      imp (allCode 19 (imp (member 6 19) (member 7 19)))
        (imp (graphFormula 6 2 2).encode (graphFormula 7 2 2).encode) :=
  certificate_correct diagonal_old_edge

/-- Pointwise diagonal coverage after a successor extension, from the
displayed successor cases, old-entry inclusion, old coverage, and the
adjoined point and pair witnesses. These are explicit hypotheses. -/
def diagonal_coverage_step : KDerivation
    (imp (imp (member 1 2) (either (equal 2 0) (member 0 2)))
      (imp (allCode 19 (imp (member 6 19) (member 7 19)))
        (imp (imp (member 0 2) (graphFormula 6 2 2).encode)
          (imp (member 7 8) (imp (pairFormula 8 0 0).encode
            (imp (member 1 2) (graphFormula 7 2 2).encode)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let C := imp (member 1 2) (either (equal 2 0) (member 0 2))
  let I := allCode 19 (imp (member 6 19) (member 7 19))
  let O := imp (member 0 2) (graphFormula 6 2 2).encode
  let P := (pairFormula 8 0 0).encode
  let Γ := [member 1 2,P,member 7 8,O,I,C]
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 7 8) := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hn : Context Γ (member 1 2) := .hypothesis (by simp [Γ])
  have hcases : Context Γ (either (equal 2 0) (member 0 2)) := .mp hn hc
  apply Context.disjunctionElim hcases
  · have he : Context (equal 2 0 :: Γ) (equal 2 0) := Context.head _ _
    exact .mp (Context.eqSymm he)
      (.mp (Context.under hp _) (.mp (Context.under hm _) (.closed diagonal_new_edge)))
  · have ha : Context (member 0 2 :: Γ) (member 0 2) := Context.head _ _
    have hedge : Context (member 0 2 :: Γ) (graphFormula 6 2 2).encode :=
      .mp ha (Context.under ho _)
    exact .mp hedge (.mp (Context.under hi _) (.closed diagonal_old_edge))

theorem diagonal_coverage_step_certificate :
    theoremCode (certificate diagonal_coverage_step) =
      imp (imp (member 1 2) (either (equal 2 0) (member 0 2)))
        (imp (allCode 19 (imp (member 6 19) (member 7 19)))
          (imp (imp (member 0 2) (graphFormula 6 2 2).encode)
            (imp (member 7 8) (imp (pairFormula 8 0 0).encode
              (imp (member 1 2) (graphFormula 7 2 2).encode))))) :=
  certificate_correct diagonal_coverage_step

end PASoundness.PAtoCompactDiagonalExtension

#print axioms PASoundness.PAtoCompactDiagonalExtension.diagonal_new_edge
#print axioms PASoundness.PAtoCompactDiagonalExtension.diagonal_new_edge_certificate
#print axioms PASoundness.PAtoCompactDiagonalExtension.diagonal_old_edge
#print axioms PASoundness.PAtoCompactDiagonalExtension.diagonal_old_edge_certificate
#print axioms PASoundness.PAtoCompactDiagonalExtension.diagonal_coverage_step
#print axioms PASoundness.PAtoCompactDiagonalExtension.diagonal_coverage_step_certificate
