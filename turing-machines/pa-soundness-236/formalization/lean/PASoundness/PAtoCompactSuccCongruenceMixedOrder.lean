import PASoundness.PAtoCompactTransitiveClosure

/-! Pointwise mixed old/top order comparisons for a conditional K successor
isomorphism argument. The two old-domain transitivity hypotheses and endpoint
membership are explicit; no graph, successor, quotient, or collection theorem
is asserted here. Literal code 1 is member 0 0, so K explosion is syntactic
and is not an assertion that all raw K models are irreflexive. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceMixedOrder
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure

def endpoints : Nat := both (member 0 2) (member 1 3)
def sourceTrans : Nat := transitiveCode 0 37 38
def targetTrans : Nat := transitiveCode 1 37 38

def oldToTop : Nat := both (imp (member 0 2) (member 1 3)) (imp (member 1 3) (member 0 2))
def topToOld : Nat := both (imp (member 2 0) (member 3 1)) (imp (member 3 1) (member 2 0))
def topToTop : Nat := both (imp (member 0 0) (member 1 1)) (imp (member 1 1) (member 0 0))

/-- An old source and its old target both lie below the respective top. -/
def old_to_top : KDerivation (imp endpoints oldToTop) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [endpoints]
  have he : Context Γ endpoints := Context.head [] _
  have ha : Context Γ (member 0 2) := Context.conjunctionLeft he
  have hb : Context Γ (member 1 3) := Context.conjunctionRight he
  have hab : Context Γ (imp (member 0 2) (member 1 3)) :=
    Context.deduction (Context.under hb _)
  have hba : Context Γ (imp (member 1 3) (member 0 2)) :=
    Context.deduction (Context.under ha _)
  exact Context.conjunctionIntro hab hba

/-- Both reverse mixed comparisons follow from transitivity and endpoint
membership. The two possible two-cycles yield literal code 1 in K. -/
def top_to_old : KDerivation (imp sourceTrans (imp targetTrans (imp endpoints topToOld))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [endpoints,targetTrans,sourceTrans]
  have he : Context Γ endpoints := .hypothesis (by simp [Γ])
  have hs : Context Γ sourceTrans := .hypothesis (by simp [Γ])
  have ht : Context Γ targetTrans := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 0 2) := Context.conjunctionLeft he
  have hb : Context Γ (member 1 3) := Context.conjunctionRight he
  have hforward : Context Γ (imp (member 2 0) (member 3 1)) := by
    apply Context.deduction
    let Δ := member 2 0 :: Γ
    have hback : Context Δ (member 2 0) := Context.head Γ _
    have hself : Context Δ (member 0 0) :=
      .mp hback (.mp (Context.under ha _) (.mp (Context.under hs _)
        (.closed (transitive_chain 0 37 38 2 0 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)))))
    have hfalse : Context Δ 1 := .mp hself (.closed (self_membership_implies_code_one 0))
    exact Context.explode (member 3 1) hfalse
  have hbackward : Context Γ (imp (member 3 1) (member 2 0)) := by
    apply Context.deduction
    let Δ := member 3 1 :: Γ
    have hback : Context Δ (member 3 1) := Context.head Γ _
    have hself : Context Δ (member 1 1) :=
      .mp hback (.mp (Context.under hb _) (.mp (Context.under ht _)
        (.closed (transitive_chain 1 37 38 3 1 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)))))
    have hfalse : Context Δ 1 := .mp hself (.closed (self_membership_implies_code_one 1))
    exact Context.explode (member 2 0) hfalse
  exact Context.conjunctionIntro hforward hbackward

/-- The two top self-comparisons are equivalent in the literal K encoding:
each self-membership entails code 1, from which every formula follows. -/
def top_to_top : KDerivation topToTop := by
  have h01 : KDerivation (imp (member 0 0) (member 1 1)) := by
    change KDerivation (imp 1 (member 1 1))
    exact explosion (member 1 1)
  have h10 : KDerivation (imp (member 1 1) (member 0 0)) :=
    self_membership_implies_code_one 1
  exact Context.closeEmpty (Context.conjunctionIntro (.closed h01) (.closed h10))

theorem old_to_top_certificate : theoremCode (certificate old_to_top) = imp endpoints oldToTop :=
  certificate_correct old_to_top

theorem top_to_old_certificate : theoremCode (certificate top_to_old) =
    imp sourceTrans (imp targetTrans (imp endpoints topToOld)) := certificate_correct top_to_old

theorem top_to_top_certificate : theoremCode (certificate top_to_top) = topToTop :=
  certificate_correct top_to_top

end PASoundness.PAtoCompactSuccCongruenceMixedOrder

#print axioms PASoundness.PAtoCompactSuccCongruenceMixedOrder.old_to_top
#print axioms PASoundness.PAtoCompactSuccCongruenceMixedOrder.top_to_old
#print axioms PASoundness.PAtoCompactSuccCongruenceMixedOrder.top_to_top
#print axioms PASoundness.PAtoCompactSuccCongruenceMixedOrder.top_to_old_certificate
