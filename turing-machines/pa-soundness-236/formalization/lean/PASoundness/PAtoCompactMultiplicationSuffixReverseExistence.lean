import PASoundness.PAtoCompactMultiplicationSuffixRowPreimage
import PASoundness.PAtoCompactAdjunction

/-! A finite K packaging step for the suffix case of multiplication's reverse
product clause. The fixed-first row witness and source successor are supplied;
this proves existence only, not uniqueness or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSuffixReverseExistence
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactMultiplicationSuffixRowPreimage
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A represented nested product edge in the extended graph 64. -/
def triple64 (a b c : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 a b) (graphFormula 64 18 c))

/-- The reverse-clause preimage at queried output 5, omitting uniqueness. -/
def reversePreimageBody (a b : Nat) : Formula := namedBoth (.member 38 a)
  (namedBoth (.member 31 b) (triple64 a b 5))

def reversePreimage : Formula := .ex 3 (.ex 4 (reversePreimageBody 3 4))

private def pairEdgeBody : Formula := namedBoth (pairFormula 18 30 41) (graphFormula 64 18 5)
private def minorBody : Formula := reversePreimageBody 30 4
private def majorBody : Formula := .ex 4 (reversePreimageBody 3 4)

/-- K turns the supplied row edge into a full source-pair preimage. The major
coordinate is the old first factor 30 and belongs to its successor 38; the
same pair witness obtained from the row is reused. No uniqueness of pair
representatives is used. -/
def reverse_preimage_from_row : KDerivation
    (imp (successorCode 30 38 39) (imp rowPreimage.encode reversePreimage.encode)) := by
  let S := successorCode 30 38 39
  let P := rowPreimageBody.encode
  let T := reversePreimage.encode
  have hminor := exists_variable_intro 4 41 minorBody (by decide) (by decide) (by decide)
  have hmshape : replace 4 41 minorBody = reversePreimageBody 30 41 := by decide
  rw [hmshape] at hminor
  have hmajor := exists_variable_intro 3 30 majorBody (by decide) (by decide) (by decide)
  have hMshape : replace 3 30 majorBody = .ex 4 minorBody := by decide
  rw [hMshape] at hmajor
  have hpair := exists_variable_intro 18 12 pairEdgeBody (by decide) (by decide) (by decide)
  have hPshape : replace 18 12 pairEdgeBody =
      namedBoth (pairFormula 12 30 41) (graphFormula 64 12 5) := by decide
  rw [hPshape] at hpair
  have hlocal : KDerivation (imp S (imp P T)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [P,S]
    have hp : Context Γ P := .head _ _
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hparts : Context Γ (both (member 31 41)
        (both (pairFormula 12 30 41).encode (graphFormula 64 12 5).encode)) := by
      simpa [P,rowPreimageBody,namedBoth,Formula.encode,Formula.not,both,neg] using hp
    have hmem := Context.conjunctionLeft hparts
    have hedge := Context.conjunctionRight hparts
    have htriple : Context Γ (triple64 30 41 5).encode := by
      have h := Context.mp hedge (.closed hpair)
      simpa [triple64,pairEdgeBody,Formula.encode] using h
    have hmajorMem : Context Γ (member 38 30) :=
      .mp hs (.closed (successor_contains_input 30 38 39 (by decide) (by decide)))
    have hw : Context Γ (reversePreimageBody 30 41).encode := by
      simpa [reversePreimageBody,namedBoth,Formula.encode,Formula.not,both,neg] using
        (Context.conjunctionIntro hmajorMem (Context.conjunctionIntro hmem htriple))
    have hex4 : Context Γ (existsCode 4 minorBody.encode) := .mp hw (.closed hminor)
    have hex3 : Context Γ (existsCode 3 majorBody.encode) := .mp hex4 (.closed hmajor)
    change Context Γ reversePreimage.encode
    exact hex3
  have hvS12 : KDerivation (imp S (allCode 12 S)) := by
    have h := (namedSuccessor 30 38 39).vacuity 12 (by decide)
    simpa [S,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
      Formula.not,successorCode,both,neg,either] using h
  have hvS41 : KDerivation (imp S (allCode 41 S)) := by
    have h := (namedSuccessor 30 38 39).vacuity 41 (by decide)
    simpa [S,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
      Formula.not,successorCode,both,neg,either] using h
  have h12 := conditionalExistsCongr 12 hvS12 hlocal
  have h12elim : KDerivation (imp (existsCode 12 T) T) := by
    have h := (ProofEquiv.vacuousExists 12 reversePreimage (by decide)).backward
    simpa [T,Formula.encode] using h
  have hmid : KDerivation (imp S (imp (existsCode 12 P) T)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [existsCode 12 P,S]
    have he : Context Γ (existsCode 12 P) := .head _ _
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    exact .mp (.mp he (.mp hs (.closed h12))) (.closed h12elim)
  have h41 := conditionalExistsCongr 41 hvS41 hmid
  have h41elim : KDerivation (imp (existsCode 41 T) T) := by
    have h := (ProofEquiv.vacuousExists 41 reversePreimage (by decide)).backward
    simpa [T,Formula.encode] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [rowPreimage.encode,S]
  have he' : Context Γ rowPreimage.encode := .head _ _
  have he : Context Γ (existsCode 41 (existsCode 12 P)) := by
    change Context Γ (existsCode 41 (existsCode 12 P)) at he'
    exact he'
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  exact .mp (.mp he (.mp hs (.closed h41))) (.closed h41elim)

theorem reverse_preimage_from_row_certificate : theoremCode (certificate reverse_preimage_from_row) =
    imp (successorCode 30 38 39) (imp rowPreimage.encode reversePreimage.encode) :=
  certificate_correct reverse_preimage_from_row
end PASoundness.PAtoCompactMultiplicationSuffixReverseExistence
#print axioms PASoundness.PAtoCompactMultiplicationSuffixReverseExistence.reverse_preimage_from_row
#print axioms PASoundness.PAtoCompactMultiplicationSuffixReverseExistence.reverse_preimage_from_row_certificate
