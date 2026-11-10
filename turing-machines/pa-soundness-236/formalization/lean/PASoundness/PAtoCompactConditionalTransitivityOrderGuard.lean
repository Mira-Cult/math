import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactDerivations

/-! Guarded pointwise composition of two literal K order instances.

Both guarded order instances and every displayed domain/edge guard are
explicitly supplied. This module neither constructs the graph edges nor
quantifies over them. In particular no condition is imposed on junk edges
outside the declared domains. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityOrderGuard
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The source and intermediate guards for the first graph. -/
def firstGuard : Nat :=
  both (member 0 2) (both (member 0 4) (both (member 1 10)
    (both (member 1 11) (both (graphFormula 6 2 10).encode
      (graphFormula 6 4 11).encode))))

/-- The intermediate and target guards for the second graph. -/
def secondGuard : Nat :=
  both (member 1 10) (both (member 1 11) (both (member 8 3)
    (both (member 8 5) (both (graphFormula 7 10 3).encode
      (graphFormula 7 11 5).encode))))

def sameOrder (a b : Nat) : Nat := both (imp a b) (imp b a)

def firstPoint : Nat := imp firstGuard (sameOrder (member 4 2) (member 11 10))
def secondPoint : Nat := imp secondGuard (sameOrder (member 11 10) (member 5 3))

/-- Given both guarded order instances and both explicit guard bundles, K
derives the corresponding pointwise source-to-target order equivalence. -/
def guarded_order_point : KDerivation
    (imp firstPoint (imp secondPoint
      (imp (both firstGuard secondGuard) (sameOrder (member 4 2) (member 5 3))))) := by
  let A := member 4 2
  let B := member 11 10
  let C := member 5 3
  let G := both firstGuard secondGuard
  let Γ := [G, secondPoint, firstPoint]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hg : Context Γ G := Context.head _ _
  have hf : Context Γ firstPoint := .hypothesis (by simp [Γ])
  have hs : Context Γ secondPoint := .hypothesis (by simp [Γ])
  have hab : Context Γ (sameOrder A B) := .mp (Context.conjunctionLeft hg) hf
  have hbc : Context Γ (sameOrder B C) := .mp (Context.conjunctionRight hg) hs
  have hab' : Context Γ (imp A B) := Context.conjunctionLeft hab
  have hba : Context Γ (imp B A) := Context.conjunctionRight hab
  have hbc' : Context Γ (imp B C) := Context.conjunctionLeft hbc
  have hcb : Context Γ (imp C B) := Context.conjunctionRight hbc
  have hac : Context Γ (imp A C) := by
    apply Context.deduction
    have ha : Context (A :: Γ) A := Context.head _ _
    exact .mp (.mp ha (.under hab' A)) (.under hbc' A)
  have hca : Context Γ (imp C A) := by
    apply Context.deduction
    have hc : Context (C :: Γ) C := Context.head _ _
    exact .mp (.mp hc (.under hcb C)) (.under hba C)
  exact Context.conjunctionIntro hac hca

theorem guarded_order_point_certificate :
    theoremCode (certificate guarded_order_point) =
      imp firstPoint (imp secondPoint
        (imp (both firstGuard secondGuard) (sameOrder (member 4 2) (member 5 3)))) :=
  certificate_correct guarded_order_point

end PASoundness.PAtoCompactConditionalTransitivityOrderGuard

#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderGuard.guarded_order_point
#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderGuard.guarded_order_point_certificate
