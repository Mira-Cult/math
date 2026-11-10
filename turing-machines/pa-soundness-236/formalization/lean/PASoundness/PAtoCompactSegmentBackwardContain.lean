import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactSegmentOrderPoint

/-! Backward containment for an initial-segment restriction, using the
explicit K derivation of the displayed guarded comparison.
The outer target transitivity and all membership/edge hypotheses are retained;
this module does not construct a restricted graph or assert a quotient law.
Compact code 1 is literal `member 0 0`. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentBackwardContain
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The target set 1 is transitive and 5∈1, hence every 3∈5 lies in 1. -/
def target_outer_member : KDerivation
    (imp (transitiveCode 1 16 18)
      (imp (member 1 5) (imp (member 5 3) (member 1 3)))) :=
  transitive_chain 1 16 18 5 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- Pointwise inverse image containment from a supplied K derivation of the
exact order comparison. Names are syntax labels, not inequalities of objects. -/
def backward_contain_of_comparison
    (order : KDerivation (imp orderFormula.encode
      (imp (member 0 7) (imp (member 0 2) (imp (member 1 3) (imp (member 1 5)
        (imp (graphFormula 6 7 3).encode (imp (graphFormula 6 2 5).encode
          (both (imp (member 2 7) (member 5 3))
            (imp (member 5 3) (member 2 7))))))))))) :
    KDerivation (imp (transitiveCode 1 16 18) (imp (member 0 2)
      (imp (member 1 5) (imp (member 5 3) (imp (member 0 7)
        (imp (graphFormula 6 2 5).encode (imp (graphFormula 6 7 3).encode
          (imp orderFormula.encode (member 2 7))))))))) := by
  let T := transitiveCode 1 16 18
  let U := member 0 2
  let V := member 1 5
  let N := member 5 3
  let W := member 0 7
  let G := (graphFormula 6 2 5).encode
  let H := (graphFormula 6 7 3).encode
  let O := orderFormula.encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [O,H,G,W,N,V,U,T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hv : Context Γ V := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hw : Context Γ W := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .head _ _
  have hc : Context Γ (member 1 3) := .mp hn (.mp hv (.mp ht (.closed target_outer_member)))
  have hi : Context Γ (both (imp (member 2 7) (member 5 3))
      (imp (member 5 3) (member 2 7))) :=
    .mp hg (.mp hh (.mp hv (.mp hc (.mp hu (.mp hw (.mp ho (.closed order)))))))
  exact .mp hn (Context.conjunctionRight hi)

theorem backward_contain_of_comparison_certificate
    (order : KDerivation (imp orderFormula.encode
      (imp (member 0 7) (imp (member 0 2) (imp (member 1 3) (imp (member 1 5)
        (imp (graphFormula 6 7 3).encode (imp (graphFormula 6 2 5).encode
          (both (imp (member 2 7) (member 5 3))
            (imp (member 5 3) (member 2 7))))))))))) :
    theoremCode (certificate (backward_contain_of_comparison order)) =
      imp (transitiveCode 1 16 18) (imp (member 0 2)
        (imp (member 1 5) (imp (member 5 3) (imp (member 0 7)
          (imp (graphFormula 6 2 5).encode (imp (graphFormula 6 7 3).encode
            (imp orderFormula.encode (member 2 7)))))))) :=
  certificate_correct (backward_contain_of_comparison order)

/-- K derives the exact pointwise containment from the displayed hypotheses;
the order comparison is supplied by the separate finite K derivation. -/
def backward_contain : KDerivation (imp (transitiveCode 1 16 18) (imp (member 0 2)
    (imp (member 1 5) (imp (member 5 3) (imp (member 0 7)
      (imp (graphFormula 6 2 5).encode (imp (graphFormula 6 7 3).encode
        (imp orderFormula.encode (member 2 7))))))))) :=
  backward_contain_of_comparison PASoundness.PAtoCompactSegmentOrderPoint.guarded_segment_order

theorem backward_contain_certificate : theoremCode (certificate backward_contain) =
    imp (transitiveCode 1 16 18) (imp (member 0 2)
      (imp (member 1 5) (imp (member 5 3) (imp (member 0 7)
        (imp (graphFormula 6 2 5).encode (imp (graphFormula 6 7 3).encode
          (imp orderFormula.encode (member 2 7)))))))) :=
  certificate_correct backward_contain

end PASoundness.PAtoCompactSegmentBackwardContain

#print axioms PASoundness.PAtoCompactSegmentBackwardContain.backward_contain_of_comparison
#print axioms PASoundness.PAtoCompactSegmentBackwardContain.backward_contain
#print axioms PASoundness.PAtoCompactSegmentBackwardContain.backward_contain_certificate
