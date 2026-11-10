import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactTransitiveClosure

/-! An old-edge case in composition-graph extension. The path formula is an
arbitrary supplied code, and both the old pointwise implication and the
successor graph are object-level hypotheses. No graph collection or induction
is asserted; code 1 remains literal compact bottom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionBackwardOld
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A supplied old edge yields the old prefix membership and arbitrary path;
the successor graph carries that membership to the next prefix. -/
def old_backward_branch (path : Nat) : KDerivation
    (imp (successorCode 10 13 15)
      (imp (imp (graphFormula 9 2 3).encode (both (member 10 2) path))
        (imp (graphFormula 9 2 3).encode (both (member 13 2) path)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let G := (graphFormula 9 2 3).encode
  let B := imp G (both (member 10 2) path)
  let S := successorCode 10 13 15
  let Γ := [G,B,S]
  have hg : Context Γ G := Context.head _ _
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hp : Context Γ (both (member 10 2) path) := .mp hg hb
  have hm : Context Γ (member 10 2) := Context.conjunctionLeft hp
  have hpath : Context Γ path := Context.conjunctionRight hp
  have hc : Context Γ (either (equal 2 10) (member 10 2)) :=
    Context.disjunctionRight (a := equal 2 10) hm
  have hn : Context Γ (member 13 2) :=
    .mp hc (.mp hs (.closed (successor_include 10 13 15 2 (by decide) (by decide) (by decide))))
  exact Context.conjunctionIntro hn hpath

theorem old_backward_branch_certificate (path : Nat) :
    theoremCode (certificate (old_backward_branch path)) =
      imp (successorCode 10 13 15)
        (imp (imp (graphFormula 9 2 3).encode (both (member 10 2) path))
          (imp (graphFormula 9 2 3).encode (both (member 13 2) path))) :=
  certificate_correct (old_backward_branch path)

end PASoundness.PAtoCompactPartialCompositionBackwardOld

#print axioms PASoundness.PAtoCompactPartialCompositionBackwardOld.old_backward_branch
#print axioms PASoundness.PAtoCompactPartialCompositionBackwardOld.old_backward_branch_certificate
