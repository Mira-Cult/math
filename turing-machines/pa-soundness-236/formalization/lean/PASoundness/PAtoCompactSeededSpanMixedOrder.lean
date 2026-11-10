import PASoundness.PAtoCompactSeededSpanOrderCases
import PASoundness.PAtoCompactAdditionMixedOrderPair

/-! The two mixed cases of seeded-span order follow from the explicit local
prefix/outside comparison guards. This does not derive those guards from the
seed or path edges, nor does it prove the seed/seed or path/path cases. -/
namespace PASoundness.PAtoCompactSeededSpanMixedOrder

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactAdditionMixedOrderPair PASoundness.PAtoCompactSeededSpanOrderCases

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def forwardSourceGuard (cut : Nat) : Nat := mixedGuard 0 cut 2 26
def forwardTargetGuard (cut : Nat) : Nat := mixedGuard 8 cut 3 27
def reverseSourceGuard (cut : Nat) : Nat := mixedGuard 0 cut 26 2
def reverseTargetGuard (cut : Nat) : Nat := mixedGuard 8 cut 27 3

/-- The four guards are supplied only in the corresponding mixed edge case. -/
def mixedPremises (sourceCut targetCut : Nat) : Nat :=
  both (imp firstSeed (imp secondPath (forwardSourceGuard sourceCut)))
    (both (imp firstSeed (imp secondPath (forwardTargetGuard targetCut)))
      (both (imp firstPath (imp secondSeed (reverseSourceGuard sourceCut)))
        (imp firstPath (imp secondSeed (reverseTargetGuard targetCut)))))

def mixedConclusions : Nat := both (imp firstSeed (imp secondPath comparison))
  (imp firstPath (imp secondSeed comparison))

/-- Both mixed comparison branches follow from the actual source and target
whole/cut guards, with source/target order aligned in either orientation. -/
def mixed_order_branches (sourceCut targetCut : Nat) : KDerivation
    (imp (mixedPremises sourceCut targetCut) mixedConclusions) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [mixedPremises sourceCut targetCut]
  have hp : Context Γ (mixedPremises sourceCut targetCut) := .head _ _
  have hforward : Context Γ (imp firstSeed (imp secondPath comparison)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [secondPath,firstSeed,mixedPremises sourceCut targetCut]
    have hpath : Context Δ secondPath := .head _ _
    have hseed : Context Δ firstSeed := .hypothesis (by simp [Δ])
    have hguards : Context Δ (mixedPremises sourceCut targetCut) := .hypothesis (by simp [Δ])
    have hsg : Context Δ (forwardSourceGuard sourceCut) :=
      .mp hpath (.mp hseed (Context.conjunctionLeft hguards))
    have htg : Context Δ (forwardTargetGuard targetCut) :=
      .mp hpath (.mp hseed (Context.conjunctionLeft (Context.conjunctionRight hguards)))
    have hagree : Context Δ (both comparison
        (both (imp (member 2 26) (member 3 27)) (imp (member 3 27) (member 2 26)))) :=
      .mp htg (.mp hsg (.closed (mixed_order_agreement 0 sourceCut 2 26 8 targetCut 3 27)))
    exact Context.conjunctionLeft hagree
  have hreverse : Context Γ (imp firstPath (imp secondSeed comparison)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [secondSeed,firstPath,mixedPremises sourceCut targetCut]
    have hseed : Context Δ secondSeed := .head _ _
    have hpath : Context Δ firstPath := .hypothesis (by simp [Δ])
    have hguards : Context Δ (mixedPremises sourceCut targetCut) := .hypothesis (by simp [Δ])
    have hsg : Context Δ (reverseSourceGuard sourceCut) :=
      .mp hseed (.mp hpath (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hguards))))
    have htg : Context Δ (reverseTargetGuard targetCut) :=
      .mp hseed (.mp hpath (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hguards))))
    have hagree : Context Δ (both
        (both (imp (member 2 26) (member 3 27)) (imp (member 3 27) (member 2 26))) comparison) :=
      .mp htg (.mp hsg (.closed (mixed_order_agreement 0 sourceCut 26 2 8 targetCut 27 3)))
    exact Context.conjunctionRight hagree
  exact Context.conjunctionIntro hforward hreverse

theorem mixed_order_branches_certificate (sourceCut targetCut : Nat) :
    theoremCode (certificate (mixed_order_branches sourceCut targetCut)) =
      imp (mixedPremises sourceCut targetCut) mixedConclusions :=
  certificate_correct (mixed_order_branches sourceCut targetCut)

end PASoundness.PAtoCompactSeededSpanMixedOrder

#print axioms PASoundness.PAtoCompactSeededSpanMixedOrder.forwardSourceGuard
#print axioms PASoundness.PAtoCompactSeededSpanMixedOrder.forwardTargetGuard
#print axioms PASoundness.PAtoCompactSeededSpanMixedOrder.reverseSourceGuard
#print axioms PASoundness.PAtoCompactSeededSpanMixedOrder.reverseTargetGuard
#print axioms PASoundness.PAtoCompactSeededSpanMixedOrder.mixedPremises
#print axioms PASoundness.PAtoCompactSeededSpanMixedOrder.mixedConclusions
#print axioms PASoundness.PAtoCompactSeededSpanMixedOrder.mixed_order_branches
#print axioms PASoundness.PAtoCompactSeededSpanMixedOrder.mixed_order_branches_certificate
