import PASoundness.PAtoCompactMultiplicationSuffixReverseExistence
import PASoundness.PAtoCompactFreeVacuity

/-! A finite K witness-preserving lift for a product reverse clause. The
retained preimage may carry extra facts (such as the chosen suffix-map edge).
Its projection and the pointwise uniqueness implication are explicit K proof
inputs. This module does not establish the preimage or uniqueness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationReverseWitnessLift
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationSuffixReverseExistence
open PASoundness.PAtoCompactFreeVacuity
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The exact reverse preimage matrix with an added supplied uniqueness
formula, retaining the same input names 3 and 4 and output 5. -/
def reverseBody (U : Formula) : Formula := namedBoth (.member 38 3)
  (namedBoth (.member 31 4) (namedBoth (triple64 3 4 5) U))

/-- Lift a retained preimage through both existentials, adding the supplied
uniqueness formula without changing either witness. The actual context H must
be free of those witness names; A may contain additional retained graph facts.
All logical implications are supplied as finite K proof data. -/
def strengthen_preimage (H A U : Formula)
    (hH3 : 3 ∉ H.free) (hH4 : 4 ∉ H.free)
    (hproj : KDerivation (imp A.encode (reversePreimageBody 3 4).encode))
    (huniq : KDerivation (imp H.encode (imp A.encode U.encode))) :
    KDerivation (imp H.encode
      (imp (existsCode 3 (existsCode 4 A.encode))
        (existsCode 3 (existsCode 4 (reverseBody U).encode)))) := by
  have hlocal : KDerivation (imp H.encode (imp A.encode (reverseBody U).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A.encode,H.encode]
    have ha : Context Γ A.encode := .head _ _
    have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
    have hp : Context Γ (reversePreimageBody 3 4).encode := .mp ha (.closed hproj)
    have hparts : Context Γ (both (member 38 3)
        (both (member 31 4) (triple64 3 4 5).encode)) := by
      simpa [reversePreimageBody,namedBoth,Formula.encode,Formula.not,both,neg] using hp
    have hu : Context Γ U.encode := .mp ha (.mp hh (.closed huniq))
    have hbody := Context.conjunctionIntro (Context.conjunctionLeft hparts)
      (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hparts))
        (Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight hparts)) hu))
    simpa [reverseBody,namedBoth,Formula.encode,Formula.not,both,neg] using hbody
  have hv4 := free_vacuity 4 H hH4
  have hv3 := free_vacuity 3 H hH3
  exact conditionalExistsCongr 3 hv3 (conditionalExistsCongr 4 hv4 hlocal)

theorem strengthen_preimage_certificate (H A U : Formula)
    (hH3 : 3 ∉ H.free) (hH4 : 4 ∉ H.free)
    (hproj : KDerivation (imp A.encode (reversePreimageBody 3 4).encode))
    (huniq : KDerivation (imp H.encode (imp A.encode U.encode))) :
    theoremCode (certificate (strengthen_preimage H A U hH3 hH4 hproj huniq)) =
      imp H.encode (imp (existsCode 3 (existsCode 4 A.encode))
        (existsCode 3 (existsCode 4 (reverseBody U).encode))) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationReverseWitnessLift
#print axioms PASoundness.PAtoCompactMultiplicationReverseWitnessLift.strengthen_preimage
#print axioms PASoundness.PAtoCompactMultiplicationReverseWitnessLift.strengthen_preimage_certificate
