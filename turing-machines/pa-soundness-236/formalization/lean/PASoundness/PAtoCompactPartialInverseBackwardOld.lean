import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactTransitiveClosure

/-! Old-edge component of the partial-inverse successor step. The old
pointwise backward invariant and the successor graph are explicit K
antecedents; no full invariant, graph existence or induction is asserted.
Compact bottom remains literal code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseBackwardOld
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldGraph : Nat := (graphFormula 7 3 2).encode
def sourceEdge : Nat := (graphFormula 6 2 3).encode
def oldBackward : Nat := imp oldGraph (both (member 8 2) sourceEdge)
def newBackwardRhs : Nat := both (member 10 2) sourceEdge

/-- An old inverse edge supplies the original source edge and a point in the
old prefix. The supplied successor graph includes every old prefix member. -/
def old_backward_branch : KDerivation
    (imp (successorCode 8 10 15) (imp oldBackward (imp oldGraph newBackwardRhs))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 8 10 15
  let Γ := [oldGraph,oldBackward,S]
  have ho : Context Γ oldGraph := Context.head _ _
  have hi : Context Γ oldBackward := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hp : Context Γ (both (member 8 2) sourceEdge) := .mp ho hi
  have hmem : Context Γ (member 8 2) := Context.conjunctionLeft hp
  have hedge : Context Γ sourceEdge := Context.conjunctionRight hp
  have hcase : Context Γ (either (equal 2 8) (member 8 2)) :=
    Context.disjunctionRight (a := equal 2 8) hmem
  have hnew : Context Γ (member 10 2) :=
    .mp hcase (.mp hs (.closed (successor_include 8 10 15 2 (by decide) (by decide) (by decide))))
  exact Context.conjunctionIntro hnew hedge

theorem old_backward_branch_certificate : theoremCode (certificate old_backward_branch) =
    imp (successorCode 8 10 15) (imp oldBackward (imp oldGraph newBackwardRhs)) :=
  certificate_correct old_backward_branch

end PASoundness.PAtoCompactPartialInverseBackwardOld

#print axioms PASoundness.PAtoCompactPartialInverseBackwardOld.old_backward_branch
#print axioms PASoundness.PAtoCompactPartialInverseBackwardOld.old_backward_branch_certificate
