import PASoundness.PAtoCompactSeededSpanOrderMixedAssembly
import PASoundness.PAtoCompactSuccCongruenceOrderAlpha
import PASoundness.PAtoCompactOrderIsoInstance
import PASoundness.PAtoCompactScopedActiveReplace

/-! Derive the seed/seed order branch from an explicit seed order and its
four actual endpoint memberships. The freshened order quantifiers allow the
second point to use 26/27 without capturing the path witness. -/
namespace PASoundness.PAtoCompactSeededSpanSeedOrder

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
open PASoundness.PAtoCompactSuccCongruenceOrderAlpha PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactSeededSpanOrderCases PASoundness.PAtoCompactSeededSpanOrderMixedAssembly

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def seedOrder : Formula := replace 6 14 (replace 1 41 (replace 0 40 oldOrderFresh))
def seedDomain : Nat := both (member 40 2) (both (member 40 26)
  (both (member 41 3) (member 41 27)))

private def frame : Formula := .imp oldOrderFresh orderMatrix
private def frame26 : Formula := replace 4 26 frame
private def frame27 : Formula := replace 5 27 frame26
private def frame40 : Formula := replace 0 40 frame27
private def frame41 : Formula := replace 1 41 frame40

private def guard : Formula := PASoundness.PAtoCompactZeroSuccessor.namedBoth (.member 40 2)
  (PASoundness.PAtoCompactZeroSuccessor.namedBoth (.member 40 26)
    (PASoundness.PAtoCompactZeroSuccessor.namedBoth (.member 41 3)
      (PASoundness.PAtoCompactZeroSuccessor.namedBoth (.member 41 27)
        (PASoundness.PAtoCompactZeroSuccessor.namedBoth (graphFormula 14 2 3) (graphFormula 14 26 27)))))
private def cmp : Formula := PASoundness.PAtoCompactZeroSuccessor.namedBoth
  (.imp (.member 26 2) (.member 27 3)) (.imp (.member 27 3) (.member 26 2))

private theorem frame_alignment : replace 6 14 frame41 = .imp seedOrder (.imp guard cmp) := by decide

/-- Given the supplied seed order and memberships in its source and target,
the two seed edges have the comparison needed by the span-order assembly. -/
def seed_seed_from_order : KDerivation (imp seedOrder.encode (imp seedDomain seedSeed)) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,Formula.encode] using compose order_unalpha order_instance
  have h26 := replace_derivation 4 26 frame (by decide) (by decide) hbase
  have h27 := replace_derivation 5 27 frame26 (by decide) (by decide)
    (by simpa only [frame26] using h26)
  have h40 := replace_derivation 0 40 frame27 (by decide) (by decide)
    (by simpa only [frame27] using h27)
  have h41 := replace_derivation 1 41 frame40 (by decide) (by decide)
    (by simpa only [frame40] using h40)
  have h14 := replace_derivation 6 14 frame41 (by decide) (by decide)
    (by simpa only [frame41] using h41)
  rw [frame_alignment] at h14
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondSeed,firstSeed,seedDomain,seedOrder.encode]
  have he2 : Context Γ secondSeed := .head _ _
  have he1 : Context Γ firstSeed := .hypothesis (by simp [Γ])
  have hd : Context Γ seedDomain := .hypothesis (by simp [Γ])
  have ho : Context Γ seedOrder.encode := .hypothesis (by simp [Γ])
  have hd1 := Context.conjunctionLeft hd
  have hd2 := Context.conjunctionLeft (Context.conjunctionRight hd)
  have hd3 := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hd))
  have hd4 := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hd))
  have hguard : Context Γ guard.encode := Context.conjunctionIntro hd1
    (Context.conjunctionIntro hd2 (Context.conjunctionIntro hd3
      (Context.conjunctionIntro hd4 (Context.conjunctionIntro he1 he2))))
  have hc : Context Γ cmp.encode := .mp hguard (.mp ho (.closed h14))
  exact hc

theorem seed_seed_from_order_certificate : theoremCode (certificate seed_seed_from_order) =
    imp seedOrder.encode (imp seedDomain seedSeed) := certificate_correct seed_seed_from_order

end PASoundness.PAtoCompactSeededSpanSeedOrder

#print axioms PASoundness.PAtoCompactSeededSpanSeedOrder.seedOrder
#print axioms PASoundness.PAtoCompactSeededSpanSeedOrder.seedDomain
#print axioms PASoundness.PAtoCompactSeededSpanSeedOrder.seed_seed_from_order
#print axioms PASoundness.PAtoCompactSeededSpanSeedOrder.seed_seed_from_order_certificate
