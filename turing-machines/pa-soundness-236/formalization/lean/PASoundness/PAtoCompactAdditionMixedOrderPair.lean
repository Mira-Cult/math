import PASoundness.PAtoCompactAdditionGenericMixedOrder

/-! Mixed-order agreement for two independently split candidate-like wholes.
Both whole/cut transitivity, local order and actual prefix/outside facts remain
literal K antecedents. Neither suffix is assumed transitive or candidate. This
is one component of sum-graph order preservation, not graph existence or a
complete addition-congruence proof. -/
namespace PASoundness.PAtoCompactAdditionMixedOrderPair

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactLocalCompareChosen PASoundness.PAtoCompactAdditionGenericMixedOrder

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact seven object-level hypotheses used for one mixed comparison. -/
def mixedGuard (whole cut old new : Nat) : Nat :=
  let p := firstTest whole cut old new
  let q := secondTest whole cut old new
  both (chosenLeast whole old new)
    (both (transitiveCode whole p q)
      (both (transitiveCode cut p q)
        (both (either (equal cut whole) (member whole cut))
          (both (member cut old) (both (member whole new) (neg (member cut new)))))))

/-- Extract the strict mixed order from the explicit guard using the proved
arbitrary-name prefix/outside theorem. -/
def mixed_facts (whole cut old new : Nat) : KDerivation
    (imp (mixedGuard whole cut old new) (both (member new old) (neg (member old new)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [mixedGuard whole cut old new]
  have h : Context Γ (mixedGuard whole cut old new) := .head _ _
  have hleast := Context.conjunctionLeft h
  have hrest := Context.conjunctionRight h
  have hw := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hc := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hcut := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hold := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hnew := Context.conjunctionLeft hrest
  have houtside := Context.conjunctionRight hrest
  have hp := prefix_before_outside whole cut old new
  exact .mp houtside (.mp hnew (.mp hold (.mp hcut (.mp hc (.mp hw (.mp hleast (.closed hp)))))))

/-- With a prefix and outside point in each whole, both forward and reverse
membership comparisons agree. Only the explicitly displayed mixed guards are
used; graph edges and their endpoint-membership proofs are separate. -/
def mixed_order_agreement (w c a b W C A B : Nat) : KDerivation
    (imp (mixedGuard w c a b) (imp (mixedGuard W C A B)
      (both (both (imp (member b a) (member B A)) (imp (member B A) (member b a)))
        (both (imp (member a b) (member A B)) (imp (member A B) (member a b)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [mixedGuard W C A B,mixedGuard w c a b]
  have htarget : Context Γ (mixedGuard W C A B) := .head _ _
  have hsource : Context Γ (mixedGuard w c a b) := .hypothesis (by simp [Γ])
  have hs := Context.mp hsource (.closed (mixed_facts w c a b))
  have ht := Context.mp htarget (.closed (mixed_facts W C A B))
  have hsf : Context Γ (member b a) := Context.conjunctionLeft hs
  have hsr : Context Γ (neg (member a b)) := Context.conjunctionRight hs
  have htf : Context Γ (member B A) := Context.conjunctionLeft ht
  have htr : Context Γ (neg (member A B)) := Context.conjunctionRight ht
  have hff : Context Γ (imp (member b a) (member B A)) := Context.lift htf (member b a)
  have hfb : Context Γ (imp (member B A) (member b a)) := Context.lift hsf (member B A)
  have hrf : Context Γ (imp (member a b) (member A B)) := by
    apply Context.deduction
    exact Context.explode _ (.mp (.head _ _) (.under hsr _))
  have hrb : Context Γ (imp (member A B) (member a b)) := by
    apply Context.deduction
    exact Context.explode _ (.mp (.head _ _) (.under htr _))
  exact Context.conjunctionIntro (Context.conjunctionIntro hff hfb)
    (Context.conjunctionIntro hrf hrb)

theorem mixed_order_agreement_certificate (w c a b W C A B : Nat) :
    theoremCode (certificate (mixed_order_agreement w c a b W C A B)) =
      imp (mixedGuard w c a b) (imp (mixedGuard W C A B)
        (both (both (imp (member b a) (member B A)) (imp (member B A) (member b a)))
          (both (imp (member a b) (member A B)) (imp (member A B) (member a b))))) :=
  certificate_correct _

end PASoundness.PAtoCompactAdditionMixedOrderPair

#print axioms PASoundness.PAtoCompactAdditionMixedOrderPair.mixedGuard
#print axioms PASoundness.PAtoCompactAdditionMixedOrderPair.mixed_facts
#print axioms PASoundness.PAtoCompactAdditionMixedOrderPair.mixed_order_agreement
#print axioms PASoundness.PAtoCompactAdditionMixedOrderPair.mixed_order_agreement_certificate
