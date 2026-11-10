import PASoundness.PAtoCompactSuffixGraphOrder
import PASoundness.PAtoCompactRestrictedOrderAlpha

/-! Exact syntax alignment of the suffix graph's quantified order clause with
the previously alpha-prepared canonical order. The coordinate binders are
renamed by the imported finite-K order_alpha proof before changing any free
endpoint/graph name. The equation below is a syntax identity; it alone does
not assert that free replacement preserves arbitrary K derivations. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixOrderAlpha
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactRestrictedOrderAlpha
open PASoundness.PAtoCompactSuffixGraphOrder
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The prepared canonical order with source 40, target 41 and graph 8.
All replacements follow the imported bound-coordinate alpha conversion. -/
def suffixAlphaOrder : Formula := replace 6 8 (replace 1 41 (replace 0 40 alphaOrder))

private def namedSuffixOrder : Formula := .all 30 (.all 31 (.all 32 (.all 33
  (.imp (namedBoth (.member 40 30) (namedBoth (.member 40 31)
    (namedBoth (.member 41 32) (namedBoth (.member 41 33)
      (namedBoth (graphFormula 8 30 32) (graphFormula 8 31 33))))))
    (namedBoth (.imp (.member 31 30) (.member 33 32))
      (.imp (.member 33 32) (.member 31 30)))))))

/-- The prepared suffix order is exactly the independently established numeric
restricted order clause. This is syntactic equality, not a K theorem that
arbitrary free-name replacement preserves proof data. -/
theorem suffix_alpha_order_code : suffixAlphaOrder.encode = suffixOrder := by
  have hs : suffixAlphaOrder = namedSuffixOrder := by decide
  rw [hs]
  rfl

end PASoundness.PAtoCompactSuffixOrderAlpha

#print axioms PASoundness.PAtoCompactSuffixOrderAlpha.suffix_alpha_order_code
