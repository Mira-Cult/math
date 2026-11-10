import PASoundness.PAtoCompactDiagonalExistentialStep

/-! Capture-safe equality transport of the supplied diagonal invariant from
names 30 and 11 to names 0 and 6. This constructs finite K proof data; it
neither asserts existence of a graph nor proves quotient reflexivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalReflexiveInvariantTransport
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactDiagonalInvariantStep PASoundness.PAtoCompactDiagonalExistentialStep

/-- Equalities of the two displayed aliases transport the exact invariant
formula to the names expected by the fixed matrix bridge. -/
def invariant_transport : KDerivation
    (imp (equal 0 30) (imp (equal 6 11)
      (imp (invariantNamed 30 11).encode oldInvariant))) := by
  have h30 := (CompactNamed.equalityReplace 30 0 (invariantNamed 30 11)
    (by decide) (by decide)).1
  have h30syntax : CompactNamed.replace 30 0 (invariantNamed 30 11) = invariantNamed 0 11 := by decide
  rw [h30syntax] at h30
  have h11 := (CompactNamed.equalityReplace 11 6 (invariantNamed 0 11)
    (by decide) (by decide)).1
  have h11syntax : CompactNamed.replace 11 6 (invariantNamed 0 11) = invariantNamed 0 6 := by decide
  rw [h11syntax, old_invariant_encode] at h11
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(invariantNamed 30 11).encode,equal 6 11,equal 0 30]
  have he0 : Context Γ (equal 0 30) := .hypothesis (by simp [Γ])
  have he6 : Context Γ (equal 6 11) := .hypothesis (by simp [Γ])
  have hi : Context Γ (invariantNamed 30 11).encode := .hypothesis (by simp [Γ])
  have hi' : Context Γ (invariantNamed 0 11).encode := .mp hi (.mp (Context.eqSymm he0) (.closed h30))
  exact .mp hi' (.mp (Context.eqSymm he6) (.closed h11))

theorem invariant_transport_certificate :
    theoremCode (certificate invariant_transport) =
      imp (equal 0 30) (imp (equal 6 11) (imp (invariantNamed 30 11).encode oldInvariant)) :=
  certificate_correct invariant_transport

end PASoundness.PAtoCompactDiagonalReflexiveInvariantTransport

#print axioms PASoundness.PAtoCompactDiagonalReflexiveInvariantTransport.invariant_transport
#print axioms PASoundness.PAtoCompactDiagonalReflexiveInvariantTransport.invariant_transport_certificate
