import PASoundness.PAtoCompactMultiplicationSuffixReverseRetained
import PASoundness.PAtoCompactMultiplicationReverseWitnessFromPoint
import PASoundness.PAtoCompactFreeVacuity

/-! Construct the exact multiplication reverse witness while the actual row
witness remains in scope. The chosen major/minor coordinates are 30 and 41;
the suffix-map edge and pair witness are retained until the supplied
uniqueness proof is used. This avoids renaming 41 to bound name 4 through a
bijection context. The uniqueness proof remains an explicit K input. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationFixedRowReverseWitness
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactMultiplicationSuffixRowPreimageRetained (rowPreimageBody rowPreimage)
open PASoundness.PAtoCompactMultiplicationSuffixReverseExistence (triple64)
open PASoundness.PAtoCompactMultiplicationSuffixCompetitorQuantify (uniqueBody)
open PASoundness.PAtoCompactMultiplicationReverseWitnessFromPoint (targetBody)
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Exact reverse uniqueness for the fixed witnesses before the outer
existentials introduce their names. -/
def fixedUnique : Formula := replace 4 41 (replace 3 30 uniqueBody)

/-- Under a supplied successor proof and fixed-witness uniqueness proof, K
maps the same retained row witnesses to the exact reverse preimage witness.
The context must be vacuous at names 12 and 41. -/
def reverse_from_fixed_row (H : Formula)
    (h12 : 12 ∉ H.free) (h41 : 41 ∉ H.free)
    (hsucc : KDerivation (imp H.encode (successorCode 30 38 39)))
    (huniq : KDerivation (imp H.encode (imp rowPreimageBody.encode fixedUnique.encode))) :
    KDerivation (imp H.encode (imp rowPreimage.encode
      (existsCode 3 (existsCode 4 targetBody.encode)))) := by
  let P := rowPreimageBody.encode
  let T := existsCode 3 (existsCode 4 targetBody.encode)
  let minorBody : Formula := replace 3 30 targetBody
  let majorBody : Formula := .ex 4 targetBody
  let pairBody : Formula := namedBoth (pairFormula 18 30 41) (graphFormula 64 18 5)
  have hminor := exists_variable_intro 4 41 minorBody (by decide) (by decide) (by decide)
  have hmajor := exists_variable_intro 3 30 majorBody (by decide) (by decide) (by decide)
  have hmajorShape : replace 3 30 majorBody = .ex 4 minorBody := by decide
  rw [hmajorShape] at hmajor
  have hpair := exists_variable_intro 18 12 pairBody (by decide) (by decide) (by decide)
  have hpairShape : replace 18 12 pairBody =
      namedBoth (pairFormula 12 30 41) (graphFormula 64 12 5) := by decide
  rw [hpairShape] at hpair
  have hchosenShape : replace 4 41 minorBody = namedBoth (.member 38 30)
      (namedBoth (.member 31 41) (namedBoth (triple64 30 41 5) fixedUnique)) := by decide
  have hlocal : KDerivation (imp H.encode (imp P T)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [P,H.encode]
    have hp : Context Γ P := .head _ _
    have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
    have hparts : Context Γ (both (member 31 41)
        (both (graphFormula 6 41 5).encode
          (both (pairFormula 12 30 41).encode (graphFormula 64 12 5).encode))) := by
      simpa [P,rowPreimageBody,namedBoth,Formula.encode,Formula.not,both,neg] using hp
    have hminorMem := Context.conjunctionLeft hparts
    have hpairs := Context.conjunctionRight (Context.conjunctionRight hparts)
    have htriple : Context Γ (triple64 30 41 5).encode := by
      have h := Context.mp hpairs (.closed hpair)
      simpa [triple64,pairBody,Formula.encode] using h
    have hmajorMem : Context Γ (member 38 30) :=
      .mp (.mp hh (.closed hsucc)) (.closed (successor_contains_input 30 38 39 (by decide) (by decide)))
    have hu : Context Γ fixedUnique.encode := .mp hp (.mp hh (.closed huniq))
    have hchosen : Context Γ (replace 4 41 minorBody).encode := by
      rw [hchosenShape]
      simpa [namedBoth,Formula.encode,Formula.not,both,neg] using
        (Context.conjunctionIntro hmajorMem (Context.conjunctionIntro hminorMem
          (Context.conjunctionIntro htriple hu)))
    have hminor' : Context Γ (existsCode 4 minorBody.encode) := .mp hchosen (.closed hminor)
    have hmajor' : Context Γ (existsCode 3 majorBody.encode) := .mp hminor' (.closed hmajor)
    simpa [T,majorBody,Formula.encode] using hmajor'
  have hvH12 := free_vacuity 12 H h12
  have hvH41 := free_vacuity 41 H h41
  have h12lift := conditionalExistsCongr 12 hvH12 hlocal
  have h12elim : KDerivation (imp (existsCode 12 T) T) := by
    let target : Formula := .ex 3 (.ex 4 targetBody)
    have h := (ProofEquiv.vacuousExists 12 target (by decide)).backward
    simpa [T,target,Formula.encode] using h
  have hmid : KDerivation (imp H.encode (imp (existsCode 12 P) T)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [existsCode 12 P,H.encode]
    have he : Context Γ (existsCode 12 P) := .head _ _
    have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
    exact .mp (.mp he (.mp hh (.closed h12lift))) (.closed h12elim)
  have h41lift := conditionalExistsCongr 41 hvH41 hmid
  have h41elim : KDerivation (imp (existsCode 41 T) T) := by
    let target : Formula := .ex 3 (.ex 4 targetBody)
    have h := (ProofEquiv.vacuousExists 41 target (by decide)).backward
    simpa [T,target,Formula.encode] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [rowPreimage.encode,H.encode]
  have he : Context Γ (existsCode 41 (existsCode 12 P)) := by
    have hh : Context Γ rowPreimage.encode := .head _ _
    simpa [rowPreimage, PAtoCompactMultiplicationSuffixRowPreimageRetained.rowPreimageAt41,
      Formula.encode,P] using hh
  have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
  exact .mp (.mp he (.mp hh (.closed h41lift))) (.closed h41elim)

theorem reverse_from_fixed_row_certificate (H : Formula)
    (h12 : 12 ∉ H.free) (h41 : 41 ∉ H.free)
    (hsucc : KDerivation (imp H.encode (successorCode 30 38 39)))
    (huniq : KDerivation (imp H.encode (imp rowPreimageBody.encode fixedUnique.encode))) :
    theoremCode (certificate (reverse_from_fixed_row H h12 h41 hsucc huniq)) =
      imp H.encode (imp rowPreimage.encode (existsCode 3 (existsCode 4 targetBody.encode))) :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationFixedRowReverseWitness
#print axioms PASoundness.PAtoCompactMultiplicationFixedRowReverseWitness.reverse_from_fixed_row
#print axioms PASoundness.PAtoCompactMultiplicationFixedRowReverseWitness.reverse_from_fixed_row_certificate
