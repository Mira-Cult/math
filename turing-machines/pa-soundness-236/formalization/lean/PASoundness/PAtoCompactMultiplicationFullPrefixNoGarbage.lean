import PASoundness.PAtoCompactFixedFirstRowGraph64

/-! Project the exact no-garbage clause from the existing full-prefix row64
invariant. This does not construct a row graph, prove a lexicographic clause,
multiplication totality, or a PA bridge. The graph and prefix labels retain
their displayed named-IR meaning; no equality of free names is assumed. -/
namespace PASoundness.PAtoCompactMultiplicationFullPrefixNoGarbage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactFixedFirstPreservedBase PASoundness.PAtoCompactFixedFirstRowGraph64
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The actual row-body witness at graph name 64 contains preservation,
coverage, and the prefix-specialized no-garbage clause. -/
theorem row_body64_expanded : rowBody64 = namedBoth (oldPreserved 64)
    (namedBoth (replace 0 31 (coverage 64)) (replace 0 31 (noGarbage 64))) := by
  rw [row_body64_shape]
  decide

/-- A finite K proof projects precisely the no-garbage clause needed by the
full-prefix lexicographic proof. The row invariant is an explicit premise. -/
def full_prefix_no_garbage : KDerivation
    (imp rowBody64.encode (replace 0 31 (noGarbage 64)).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hinv : Context [rowBody64.encode] rowBody64.encode := .head [] _
  have h : Context [rowBody64.encode] (namedBoth (oldPreserved 64)
      (namedBoth (replace 0 31 (coverage 64)) (replace 0 31 (noGarbage 64)))).encode := by
    rw [← row_body64_expanded]
    exact hinv
  change Context [rowBody64.encode] (both (oldPreserved 64).encode
    (both (replace 0 31 (coverage 64)).encode (replace 0 31 (noGarbage 64)).encode)) at h
  exact Context.conjunctionRight (Context.conjunctionRight h)

theorem full_prefix_no_garbage_certificate :
    theoremCode (certificate full_prefix_no_garbage) =
      imp rowBody64.encode (replace 0 31 (noGarbage 64)).encode :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationFullPrefixNoGarbage
#print axioms PASoundness.PAtoCompactMultiplicationFullPrefixNoGarbage.row_body64_expanded
#print axioms PASoundness.PAtoCompactMultiplicationFullPrefixNoGarbage.full_prefix_no_garbage
#print axioms PASoundness.PAtoCompactMultiplicationFullPrefixNoGarbage.full_prefix_no_garbage_certificate
