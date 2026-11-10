import PASoundness.PAtoCompactSuccCongruenceMixedOrder

/-! Pointwise old/top comparisons for old endpoint names 4 and 5, using the
same transitivity hypotheses as the 2/3 comparison. This is finite K proof
data; it does not establish graph existence or successor congruence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccMixedOrder45
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactSuccCongruenceMixedOrder

def endpoints45 : Nat := both (member 0 4) (member 1 5)
def oldToTop45 : Nat := both (imp (member 0 4) (member 1 5))
  (imp (member 1 5) (member 0 4))
def topToOld45 : Nat := both (imp (member 4 0) (member 5 1))
  (imp (member 5 1) (member 4 0))

/-- Both old endpoints lie below the respective top. -/
def old_to_top45 : KDerivation (imp endpoints45 oldToTop45) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [endpoints45]
  have he : Context Γ endpoints45 := Context.head [] _
  have ha : Context Γ (member 0 4) := Context.conjunctionLeft he
  have hb : Context Γ (member 1 5) := Context.conjunctionRight he
  exact Context.conjunctionIntro (Context.deduction (Context.under hb _))
    (Context.deduction (Context.under ha _))

/-- The reverse mixed comparisons use old-domain transitivity and the explicit
endpoint membership. Two-cycles yield literal compact code 1, not a claim of
ordinary irreflexivity in every raw K model. -/
def top_to_old45 : KDerivation
    (imp sourceTrans (imp targetTrans (imp endpoints45 topToOld45))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [endpoints45,targetTrans,sourceTrans]
  have he : Context Γ endpoints45 := .hypothesis (by simp [Γ])
  have hs : Context Γ sourceTrans := .hypothesis (by simp [Γ])
  have ht : Context Γ targetTrans := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 0 4) := Context.conjunctionLeft he
  have hb : Context Γ (member 1 5) := Context.conjunctionRight he
  have hforward : Context Γ (imp (member 4 0) (member 5 1)) := by
    apply Context.deduction
    let Δ := member 4 0 :: Γ
    have hback : Context Δ (member 4 0) := Context.head Γ _
    have hself : Context Δ (member 0 0) :=
      .mp hback (.mp (Context.under ha _) (.mp (Context.under hs _)
        (.closed (transitive_chain 0 37 38 4 0 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)))))
    have hfalse : Context Δ 1 := .mp hself (.closed (self_membership_implies_code_one 0))
    exact Context.explode (member 5 1) hfalse
  have hbackward : Context Γ (imp (member 5 1) (member 4 0)) := by
    apply Context.deduction
    let Δ := member 5 1 :: Γ
    have hback : Context Δ (member 5 1) := Context.head Γ _
    have hself : Context Δ (member 1 1) :=
      .mp hback (.mp (Context.under hb _) (.mp (Context.under ht _)
        (.closed (transitive_chain 1 37 38 5 1 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)))))
    have hfalse : Context Δ 1 := .mp hself (.closed (self_membership_implies_code_one 1))
    exact Context.explode (member 4 0) hfalse
  exact Context.conjunctionIntro hforward hbackward

theorem old_to_top45_certificate : theoremCode (certificate old_to_top45) =
    imp endpoints45 oldToTop45 := certificate_correct old_to_top45

theorem top_to_old45_certificate : theoremCode (certificate top_to_old45) =
    imp sourceTrans (imp targetTrans (imp endpoints45 topToOld45)) :=
  certificate_correct top_to_old45

end PASoundness.PAtoCompactSuccMixedOrder45

#print axioms PASoundness.PAtoCompactSuccMixedOrder45.old_to_top45
#print axioms PASoundness.PAtoCompactSuccMixedOrder45.top_to_old45
#print axioms PASoundness.PAtoCompactSuccMixedOrder45.old_to_top45_certificate
#print axioms PASoundness.PAtoCompactSuccMixedOrder45.top_to_old45_certificate
