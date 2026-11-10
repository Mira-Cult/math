import PASoundness.PAtoCompactFixedFirstPreservedBase

/-! A finite K point query of the full-prefix fixed-first row invariant.
It retains the map graph 6 and row graph 64, and constructs no row graph or
multiplication result. Output name 5 is left free for downstream uses; the
returned map-output and pair witnesses use names 11 and 12. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRowCoveragePoint41
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFixedFirstPreservedBase
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Query result: a map output and an actual represented row edge through
one explicitly supplied ordered-pair representative. -/
def pointWitness (v p : Nat) : Formula := namedBoth (graphFormula 6 41 v)
  (namedBoth (pairFormula p 30 41) (graphFormula 64 p v))

private def pointBody : Formula := .imp
  (namedBoth (.member 31 3) (.member 31 3)) (.ex 4 (.ex 5
    (namedBoth (graphFormula 6 3 4)
      (namedBoth (pairFormula 5 30 3) (graphFormula 64 5 4)))))

private theorem coverage_shape : replace 0 31 (coverage 64) = .all 3 pointBody := by decide
private theorem invariant_shape : replace 0 31 (rowInvariantPreserved 64) =
    namedBoth (oldPreserved 64)
      (namedBoth (replace 0 31 (coverage 64)) (replace 0 31 (noGarbage 64))) := by decide

/-- Each member at query name 41 has an actual row edge, after the prefix is
set to the whole source 31. The same pair witness is used on both sides of
that row edge; no uniqueness of pair representatives is assumed. -/
def coverage_point : KDerivation
    (imp (replace 0 31 (rowInvariantPreserved 64)).encode
      (imp (member 31 41)
        (existsCode 11 (existsCode 12 (pointWitness 11 12).encode)))) := by
  have hi := universalInstance 3 41 pointBody (by decide) (by decide) (by decide)
  have hshape : replace 3 41 pointBody = .imp
      (namedBoth (.member 31 41) (.member 31 41)) (.ex 4 (.ex 5 (pointWitness 4 5))) := by decide
  rw [hshape] at hi
  have hinner := (existentialAlpha 5 12 (pointWitness 4 5)
    (by decide) (by decide) (by decide)).1
  have hir : replace 5 12 (pointWitness 4 5) = pointWitness 4 12 := by decide
  rw [hir] at hinner
  have houter := existsCongr 4 hinner
  have halpha := (existentialAlpha 4 11 (.ex 12 (pointWitness 4 12))
    (by decide) (by decide) (by decide)).1
  have har : replace 4 11 (.ex 12 (pointWitness 4 12)) = .ex 12 (pointWitness 11 12) := by decide
  rw [har] at halpha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 41,(replace 0 31 (rowInvariantPreserved 64)).encode]
  have hm : Context Γ (member 31 41) := .head _ _
  have hinv : Context Γ (replace 0 31 (rowInvariantPreserved 64)).encode := .hypothesis (by simp [Γ])
  rw [invariant_shape] at hinv
  have hp : Context Γ (replace 0 31 (coverage 64)).encode := by
    have h : Context Γ (both (oldPreserved 64).encode
        (both (replace 0 31 (coverage 64)).encode (replace 0 31 (noGarbage 64)).encode)) := by
      simpa [namedBoth,Formula.not,Formula.encode,both,neg] using hinv
    exact Context.conjunctionLeft (Context.conjunctionRight h)
  rw [coverage_shape] at hp
  have hguard : Context Γ (namedBoth (.member 31 41) (.member 31 41)).encode := by
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using Context.conjunctionIntro hm hm
  have hraw : Context Γ (existsCode 4 (existsCode 5 (pointWitness 4 5).encode)) := by
    have h := Context.mp hguard (Context.mp hp (.closed hi))
    simpa [Formula.encode] using h
  exact .mp (.mp hraw (.closed houter)) (.closed halpha)

theorem coverage_point_certificate : theoremCode (certificate coverage_point) =
    imp (replace 0 31 (rowInvariantPreserved 64)).encode
      (imp (member 31 41)
        (existsCode 11 (existsCode 12 (pointWitness 11 12).encode))) :=
  certificate_correct coverage_point
end PASoundness.PAtoCompactMultiplicationRowCoveragePoint41
#print axioms PASoundness.PAtoCompactMultiplicationRowCoveragePoint41.coverage_point
#print axioms PASoundness.PAtoCompactMultiplicationRowCoveragePoint41.coverage_point_certificate
