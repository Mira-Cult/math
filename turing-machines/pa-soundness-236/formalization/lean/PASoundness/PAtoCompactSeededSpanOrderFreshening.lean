import PASoundness.PAtoCompactSeededSpanPointOrder
import PASoundness.PAtoCompactCommonSourceSpanInputMatrices

/-! Convert actual supplied order clauses to the alpha-freshened clauses used
in seeded-span pointwise order. Only bound labels change; no order clause or
graph is constructed. -/
namespace PASoundness.PAtoCompactSeededSpanOrderFreshening

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceOrderAlpha
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactSeededSpanSeedOrder

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def frame : Formula := .imp orderFormula oldOrderFresh
private def frame25 : Formula := replace 0 25 frame
private def first0 : Formula := replace 1 0 frame25
private def second8 : Formula := replace 1 8 frame25
private def second1 : Formula := replace 25 1 second8
private def seed40 : Formula := replace 0 40 frame
private def seed41 : Formula := replace 1 41 seed40

def seedOriginal : Formula := replace 6 14 (replace 1 41 (replace 0 40 orderFormula))

private def original : KDerivation frame.encode := by
  simpa only [frame,Formula.encode] using order_alpha

/-- Freshen the first supplied common-source-to-image order. -/
def first_order_fresh : KDerivation
    (imp PASoundness.PAtoCompactCommonSourceSpanInputMatrices.firstOrder.encode
      PASoundness.PAtoCompactSeededSpanSelectedPathOrder.firstOrder.encode) := by
  have h25 := replace_derivation 0 25 frame (by decide) (by decide) original
  have h0 := replace_derivation 1 0 frame25 (by decide) (by decide) (by simpa only [frame25] using h25)
  have h1 := replace_derivation 25 1 first0 (by decide) (by decide) (by simpa only [first0] using h0)
  have ha : replace 25 1 first0 = .imp PASoundness.PAtoCompactCommonSourceSpanInputMatrices.firstOrder
      PASoundness.PAtoCompactSeededSpanSelectedPathOrder.firstOrder := by decide
  rw [ha] at h1
  exact h1

/-- Freshen the second supplied common-source-to-image order. -/
def second_order_fresh : KDerivation
    (imp PASoundness.PAtoCompactCommonSourceSpanInputMatrices.secondOrder.encode
      PASoundness.PAtoCompactSeededSpanSelectedPathOrder.secondOrder.encode) := by
  have h25 := replace_derivation 0 25 frame (by decide) (by decide) original
  have h8 := replace_derivation 1 8 frame25 (by decide) (by decide) (by simpa only [frame25] using h25)
  have h1 := replace_derivation 25 1 second8 (by decide) (by decide) (by simpa only [second8] using h8)
  have h7 := replace_derivation 6 7 second1 (by decide) (by decide) (by simpa only [second1] using h1)
  have ha : replace 6 7 second1 = .imp PASoundness.PAtoCompactCommonSourceSpanInputMatrices.secondOrder
      PASoundness.PAtoCompactSeededSpanSelectedPathOrder.secondOrder := by decide
  rw [ha] at h7
  exact h7

/-- Freshen the supplied graph-14 seed order on source 40 and target 41. -/
def seed_order_fresh : KDerivation (imp seedOriginal.encode seedOrder.encode) := by
  have h40 := replace_derivation 0 40 frame (by decide) (by decide) original
  have h41 := replace_derivation 1 41 seed40 (by decide) (by decide) (by simpa only [seed40] using h40)
  have h14 := replace_derivation 6 14 seed41 (by decide) (by decide) (by simpa only [seed41] using h41)
  have ha : replace 6 14 seed41 = .imp seedOriginal seedOrder := by decide
  rw [ha] at h14
  exact h14

theorem first_order_fresh_certificate : theoremCode (certificate first_order_fresh) =
    imp PASoundness.PAtoCompactCommonSourceSpanInputMatrices.firstOrder.encode
      PASoundness.PAtoCompactSeededSpanSelectedPathOrder.firstOrder.encode := certificate_correct first_order_fresh
theorem second_order_fresh_certificate : theoremCode (certificate second_order_fresh) =
    imp PASoundness.PAtoCompactCommonSourceSpanInputMatrices.secondOrder.encode
      PASoundness.PAtoCompactSeededSpanSelectedPathOrder.secondOrder.encode := certificate_correct second_order_fresh
theorem seed_order_fresh_certificate : theoremCode (certificate seed_order_fresh) =
    imp seedOriginal.encode seedOrder.encode := certificate_correct seed_order_fresh

end PASoundness.PAtoCompactSeededSpanOrderFreshening

#print axioms PASoundness.PAtoCompactSeededSpanOrderFreshening.seedOriginal
#print axioms PASoundness.PAtoCompactSeededSpanOrderFreshening.first_order_fresh
#print axioms PASoundness.PAtoCompactSeededSpanOrderFreshening.second_order_fresh
#print axioms PASoundness.PAtoCompactSeededSpanOrderFreshening.seed_order_fresh
#print axioms PASoundness.PAtoCompactSeededSpanOrderFreshening.first_order_fresh_certificate
#print axioms PASoundness.PAtoCompactSeededSpanOrderFreshening.second_order_fresh_certificate
#print axioms PASoundness.PAtoCompactSeededSpanOrderFreshening.seed_order_fresh_certificate
