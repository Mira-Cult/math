import PASoundness.PAtoCompactFirstSuffixOrderWiden
import PASoundness.PAtoCompactFirstSpanTargetOutside

/-! Widen the second graph's order clause from suffix38 to whole8 by
capture-safe relocation of the first-side K proof. The suffix order and
stored-clean graph remain explicit antecedents. -/
namespace PASoundness.PAtoCompactSecondSuffixOrderWiden

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def suffixOrder : Formula := replace 6 7 (replace 25 1 (replace 1 38 (replace 0 25 orderFormula)))
def wholeOrder : Formula := PASoundness.PAtoCompactCommonSourceSpanInputMatrices.secondOrder
private def original : Formula := .imp PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder
  (.imp PASoundness.PAtoCompactSuffixCleanGraphGuard.storedClean PASoundness.PAtoCompactFirstSuffixOrderWiden.wholeOrder)
private def at38 : Formula := replace 31 38 original
private def at7 : Formula := replace 6 7 at38

/-- The exact second whole-domain order follows from its suffix order and
the actual graph7 stored-pair-clean condition. -/
def second_suffix_order_widen : KDerivation (imp suffixOrder.encode
    (imp targetClean.encode wholeOrder.encode)) := by
  have hbase : KDerivation original.encode := by
    simpa only [original,Formula.encode] using PASoundness.PAtoCompactFirstSuffixOrderWiden.first_suffix_order_widen
  have h38 := replace_derivation 31 38 original (by decide) (by decide) hbase
  have h7 := replace_derivation 6 7 at38 (by decide) (by decide) (by simpa only [at38] using h38)
  have h8 := replace_derivation 0 8 at7 (by decide) (by decide) (by simpa only [at7] using h7)
  have ha : replace 0 8 at7 = .imp suffixOrder (.imp targetClean wholeOrder) := by decide
  rw [ha] at h8
  exact h8

theorem second_suffix_order_widen_certificate : theoremCode (certificate second_suffix_order_widen) =
    imp suffixOrder.encode (imp targetClean.encode wholeOrder.encode) := certificate_correct second_suffix_order_widen

end PASoundness.PAtoCompactSecondSuffixOrderWiden

#print axioms PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder
#print axioms PASoundness.PAtoCompactSecondSuffixOrderWiden.wholeOrder
#print axioms PASoundness.PAtoCompactSecondSuffixOrderWiden.second_suffix_order_widen
#print axioms PASoundness.PAtoCompactSecondSuffixOrderWiden.second_suffix_order_widen_certificate
