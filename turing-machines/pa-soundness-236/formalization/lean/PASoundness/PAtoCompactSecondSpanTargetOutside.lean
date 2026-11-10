import PASoundness.PAtoCompactFirstSpanTargetOutside

/-! The second common-source path's target-side point is outside cut 41.
Instantiation of the other endpoint at 26 occurs under the fixed targetGuard,
so its internal predicate binder 26 remains unchanged. -/
namespace PASoundness.PAtoCompactSecondSpanTargetOutside

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactCommonSourceSpanBase
open PASoundness.PAtoCompactSeededSpanOrderSplit PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def frame : Formula := .imp targetGuard
  (.imp spanPath (Formula.member 41 3).not)
private def at28 : Formula := replace 2 28 frame
private def point28 : Formula := .imp (replace 3 27 (replace 2 28 spanPath))
  (Formula.member 41 27).not
private def point26 : Formula := .imp movedPath (Formula.member 41 27).not

/-- The second actual path supplies an outside-cut target-side point under
the explicitly supplied clean graph and relative-complement filter. -/
def second_path_target_outside : KDerivation (imp targetGuard.encode
    (imp movedPath.encode (neg (member 41 27)))) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,Formula.not,Formula.encode,CompactProof.neg] using first_path_target_outside
  have h28 := replace_derivation 2 28 frame (by decide) (by decide) hbase
  have h27 := replace_derivation 3 27 at28 (by decide) (by decide) (by simpa only [at28] using h28)
  have ha : replace 3 27 at28 = .imp targetGuard point28 := by decide
  rw [ha] at h27
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [targetGuard.encode]
  have hg : Context Γ targetGuard.encode := .head _ _
  have hp : Context Γ point28.encode := .mp hg (.closed h27)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 28 h)) := by
    intro h hh
    have he : h = targetGuard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 28 targetGuard (by decide)
  have hall : Context Γ (allCode 28 point28.encode) := Context.generalize 28 hv hp
  have hi := universalInstance 28 26 point28 (by decide) (by decide) (by decide)
  have hs : replace 28 26 point28 = point26 := by decide
  rw [hs] at hi
  have hpoint : Context Γ point26.encode := .mp hall (.closed hi)
  exact hpoint

theorem second_path_target_outside_certificate : theoremCode (certificate second_path_target_outside) =
    imp targetGuard.encode (imp movedPath.encode (neg (member 41 27))) :=
  certificate_correct second_path_target_outside

end PASoundness.PAtoCompactSecondSpanTargetOutside

#print axioms PASoundness.PAtoCompactSecondSpanTargetOutside.second_path_target_outside
#print axioms PASoundness.PAtoCompactSecondSpanTargetOutside.second_path_target_outside_certificate
