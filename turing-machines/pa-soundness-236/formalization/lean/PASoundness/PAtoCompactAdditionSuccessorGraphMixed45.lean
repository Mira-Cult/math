import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactTransitiveClosure

/-! Pointwise mixed old/top order comparisons for the addition-successor
graph extension at old source/target names 4 and 5. The source top is name 31
and the target top is the distinct syntactic name 32. The old target domain is
the suffix at name 34. This file
does not construct a graph, assume the denoted tops unequal, or prove addition.
Compact code 1 is the literal self-membership formula. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorGraphMixed45
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] imp Cantor.pair Cantor.triangle

def suffix : Nat := filterGraph 32 34 35 (neg (member 33 35))
def endpoints : Nat := both (member 31 4) (member 34 5)
def sourceTrans : Nat := transitiveCode 31 37 38
def targetTrans : Nat := transitiveCode 32 37 38
def oldToTop : Nat := both (imp (member 31 4) (member 32 5))
  (imp (member 32 5) (member 31 4))
def topToOld : Nat := both (imp (member 4 31) (member 5 32))
  (imp (member 5 32) (member 4 31))

/-- The top-to-top order comparison follows from literal K irreflexivity
at both (possibly equal) endpoints. -/
def top_to_top : KDerivation
    (both (imp (member 31 31) (member 32 32))
      (imp (member 32 32) (member 31 31))) := by
  apply Context.closeEmpty
  apply Context.conjunctionIntro
  · apply Context.deduction
    exact Context.explode (member 32 32)
      (.mp (Context.head [] (member 31 31)) (.closed (self_membership_implies_code_one 31)))
  · apply Context.deduction
    exact Context.explode (member 31 31)
      (.mp (Context.head [] (member 32 32)) (.closed (self_membership_implies_code_one 32)))

/-- A suffix member is below the old result at the displayed target name. -/
def suffix_point : KDerivation
    (imp suffix (imp (member 34 5) (member 32 5))) := by
  let P : Formula := (Formula.member 33 35).not
  have hi := filter_at 32 34 35 5 P (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hi' : KDerivation (imp suffix
      (both (imp (member 34 5) (both (member 32 5) (neg (member 33 5))))
        (imp (both (member 32 5) (neg (member 33 5))) (member 34 5)))) := by
    simpa [suffix,P,Formula.not,Formula.encode,replace,rename,neg] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 34 5,suffix]
  have hs : Context Γ suffix := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 34 5) := .head _ _
  have hrow := Context.mp hs (.closed hi')
  exact Context.conjunctionLeft (.mp hm (Context.conjunctionLeft hrow))

/-- Old paired endpoints both lie below the new, unequal top names. -/
def old_to_top : KDerivation (imp suffix (imp endpoints oldToTop)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [endpoints,suffix]
  have he : Context Γ endpoints := .head _ _
  have hs : Context Γ suffix := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 31 4) := Context.conjunctionLeft he
  have hb : Context Γ (member 32 5) :=
    .mp (Context.conjunctionRight he) (.mp hs (.closed suffix_point))
  exact Context.conjunctionIntro (Context.deduction (Context.under hb _))
    (Context.deduction (Context.under ha _))

/-- Reverse mixed comparisons follow from literal K transitivity at both
tops and the suffix filter. The contradictory cycles imply compact code 1. -/
def top_to_old : KDerivation
    (imp suffix (imp sourceTrans (imp targetTrans (imp endpoints topToOld)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [endpoints,targetTrans,sourceTrans,suffix]
  have he : Context Γ endpoints := .head _ _
  have hs : Context Γ sourceTrans := .hypothesis (by simp [Γ])
  have ht : Context Γ targetTrans := .hypothesis (by simp [Γ])
  have hf : Context Γ suffix := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 31 4) := Context.conjunctionLeft he
  have hb : Context Γ (member 32 5) :=
    .mp (Context.conjunctionRight he) (.mp hf (.closed suffix_point))
  have hforward : Context Γ (imp (member 4 31) (member 5 32)) := by
    apply Context.deduction
    let Δ := member 4 31 :: Γ
    have hback : Context Δ (member 4 31) := .head _ _
    have hself : Context Δ (member 31 31) :=
      .mp hback (.mp (Context.under ha _) (.mp (Context.under hs _)
        (.closed (transitive_instance 31 4 37 38 (by decide) (by decide)
          (by decide) (by decide) (by decide)))))
    exact Context.explode (member 5 32)
      (.mp hself (.closed (self_membership_implies_code_one 31)))
  have hbackward : Context Γ (imp (member 5 32) (member 4 31)) := by
    apply Context.deduction
    let Δ := member 5 32 :: Γ
    have hback : Context Δ (member 5 32) := .head _ _
    have hself : Context Δ (member 32 32) :=
      .mp hback (.mp (Context.under hb _) (.mp (Context.under ht _)
        (.closed (transitive_instance 32 5 37 38 (by decide) (by decide)
          (by decide) (by decide) (by decide)))))
    exact Context.explode (member 4 31)
      (.mp hself (.closed (self_membership_implies_code_one 32)))
  exact Context.conjunctionIntro hforward hbackward

theorem old_to_top_certificate : theoremCode (certificate old_to_top) =
    imp suffix (imp endpoints oldToTop) := certificate_correct old_to_top

theorem top_to_old_certificate : theoremCode (certificate top_to_old) =
    imp suffix (imp sourceTrans (imp targetTrans (imp endpoints topToOld))) :=
  certificate_correct top_to_old

theorem top_to_top_certificate : theoremCode (certificate top_to_top) =
    both (imp (member 31 31) (member 32 32))
      (imp (member 32 32) (member 31 31)) := certificate_correct top_to_top

end PASoundness.PAtoCompactAdditionSuccessorGraphMixed45

#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphMixed45.old_to_top
#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphMixed45.top_to_old
#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphMixed45.old_to_top_certificate
#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphMixed45.top_to_old_certificate
#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphMixed45.top_to_top
#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphMixed45.top_to_top_certificate
