import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactAdjunction

/-! Pointwise new-edge backward branch for a partial composition graph.
Selected path, endpoint equalities, and successor graph are all explicit K
antecedents. This does not establish graph existence, induction, or PA transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionBackwardNew
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

/-- The exact path body in the partial-composition invariant. -/
def pathBody : Formula := conj (.member 1 4)
  (conj (graphFormula 6 2 4) (graphFormula 7 4 3))

def path : Formula := .ex 4 pathBody

/-- A queried newly added pair is in the successor prefix and is justified
by the explicitly supplied selected path through middle element 11. -/
def new_edge_backward : KDerivation
    (imp (equal 2 10) (imp (equal 3 12) (imp (successorCode 10 13 15)
      (imp (member 1 11) (imp (graphFormula 6 10 11).encode
        (imp (graphFormula 7 11 12).encode
          (both (member 13 2) path.encode))))))) := by
  have hs := (equalityReplace 10 2 (graphFormula 6 10 11) (by decide) (by decide)).1
  have hs' : replace 10 2 (graphFormula 6 10 11) = graphFormula 6 2 11 := by decide
  rw [hs'] at hs
  have ht := (equalityReplace 12 3 (graphFormula 7 11 12) (by decide) (by decide)).1
  have ht' : replace 12 3 (graphFormula 7 11 12) = graphFormula 7 11 3 := by decide
  rw [ht'] at ht
  have hi := exists_variable_intro 4 11 pathBody (by decide) (by decide) (by decide)
  have hb : replace 4 11 pathBody = conj (.member 1 11)
      (conj (graphFormula 6 2 11) (graphFormula 7 11 3)) := by decide
  rw [hb] at hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 7 11 12).encode,(graphFormula 6 10 11).encode,
    member 1 11,successorCode 10 13 15,equal 3 12,equal 2 10]
  have he2 : Context Γ (equal 2 10) := .hypothesis (by simp [Γ])
  have he3 : Context Γ (equal 3 12) := .hypothesis (by simp [Γ])
  have hsucc : Context Γ (successorCode 10 13 15) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 11) := .hypothesis (by simp [Γ])
  have hf : Context Γ (graphFormula 6 10 11).encode := .hypothesis (by simp [Γ])
  have hg : Context Γ (graphFormula 7 11 12).encode := Context.head _ _
  have htop : Context Γ (member 13 10) :=
    .mp hsucc (.closed (successor_contains_input 10 13 15 (by decide) (by decide)))
  have hquery : Context Γ (member 13 2) :=
    .mp (Context.eqSymm he2) (.mp htop (.closed (memberRightEquality 13 10 2)))
  have hf' : Context Γ (graphFormula 6 2 11).encode :=
    .mp hf (.mp (Context.eqSymm he2) (.closed hs))
  have hg' : Context Γ (graphFormula 7 11 3).encode :=
    .mp hg (.mp (Context.eqSymm he3) (.closed ht))
  have hbody : Context Γ (conj (.member 1 11)
      (conj (graphFormula 6 2 11) (graphFormula 7 11 3))).encode :=
    Context.conjunctionIntro hm (Context.conjunctionIntro hf' hg')
  have hp : Context Γ path.encode := .mp hbody (.closed hi)
  exact Context.conjunctionIntro hquery hp

theorem new_edge_backward_certificate : theoremCode (certificate new_edge_backward) =
    imp (equal 2 10) (imp (equal 3 12) (imp (successorCode 10 13 15)
      (imp (member 1 11) (imp (graphFormula 6 10 11).encode
        (imp (graphFormula 7 11 12).encode
          (both (member 13 2) path.encode)))))) := certificate_correct new_edge_backward

end PASoundness.PAtoCompactPartialCompositionBackwardNew

#print axioms PASoundness.PAtoCompactPartialCompositionBackwardNew.new_edge_backward
#print axioms PASoundness.PAtoCompactPartialCompositionBackwardNew.new_edge_backward_certificate
