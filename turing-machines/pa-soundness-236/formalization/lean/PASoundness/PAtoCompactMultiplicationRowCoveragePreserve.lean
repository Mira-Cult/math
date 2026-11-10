import PASoundness.PAtoCompactMultiplicationRowGraphPreserve

/-! A literal K lifting of old multiplication-row coverage across one graph
adjunction. The new graph keeps the same witnesses for every previously
covered index. The new prefix point, no-garbage and row existence are separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRowCoveragePreserve
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationRowGraphPreserve
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Both the candidate prefix 0 and the row index domain 31 contain index 3. -/
def indexGuard : Formula := namedBoth (.member 0 3) (.member 31 3)

/-- Every guarded index has a supplied map edge and a covered nested-pair
edge in graph g. This definition is syntactic for arbitrary g; the theorem
below uses only the fixed capture-safe labels 11 and 12. -/
def coverageAll (g : Nat) : Formula := .all 3 (.imp indexGuard (coverage g))

private def guarded_point_step : KDerivation (imp extension.encode
    (imp (Formula.imp indexGuard (coverage 11)).encode
      (Formula.imp indexGuard (coverage 12)).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [indexGuard.encode, (Formula.imp indexGuard (coverage 11)).encode, extension.encode]
  have hi : Context Γ indexGuard.encode := .head _ _
  have hc : Context Γ (imp indexGuard.encode (coverage 11).encode) := .hypothesis (by simp [Γ, Formula.encode])
  have he : Context Γ extension.encode := .hypothesis (by simp [Γ])
  have ho : Context Γ (coverage 11).encode := .mp hi hc
  exact .mp ho (.mp he (.closed coverage_preserved))

/-- Every index covered by old graph 11 remains covered by new graph 12 after
adjoining point 13, uniformly over indices in prefix 0 and row domain 31. -/
def coverage_all_preserved : KDerivation (imp extension.encode
    (imp (coverageAll 11).encode (coverageAll 12).encode)) := by
  have hv : KDerivation (imp extension.encode (allCode 3 extension.encode)) :=
    extension.vacuity 3 (by decide)
  exact conditionalAllCongr 3 hv guarded_point_step

theorem coverage_all_preserved_certificate : theoremCode (certificate coverage_all_preserved) =
    imp extension.encode (imp (coverageAll 11).encode (coverageAll 12).encode) :=
  certificate_correct coverage_all_preserved
end PASoundness.PAtoCompactMultiplicationRowCoveragePreserve
#print axioms PASoundness.PAtoCompactMultiplicationRowCoveragePreserve.coverage_all_preserved
#print axioms PASoundness.PAtoCompactMultiplicationRowCoveragePreserve.coverage_all_preserved_certificate
