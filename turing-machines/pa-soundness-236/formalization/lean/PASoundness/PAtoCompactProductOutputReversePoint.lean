import PASoundness.PAtoCompactProductOutputReverseReconstruct
import PASoundness.PAtoCompactFreeVacuity

/-! For a target member, select one source preimage and its factor coordinates
and reconstruct their forward path body under the same witnesses. This is
pointwise existence, not yet graph reverse coverage or uniqueness. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputReversePoint

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductOutputImagePoint
open PASoundness.PAtoCompactProductOutputPreimagePoint PASoundness.PAtoCompactProductOutputReverseReconstruct

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def pointGuard : Formula := namedBoth sourceMatrix (namedBoth firstBijection (.member 42 33))

def point_reconstruct : KDerivation (imp pointGuard.encode
    (imp PAtoCompactProductOutputPreimagePoint.pairedBody.encode reconstructed.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [PAtoCompactProductOutputPreimagePoint.pairedBody.encode,pointGuard.encode]
  have hp : Context Γ PAtoCompactProductOutputPreimagePoint.pairedBody.encode := .head _ _
  have hg : Context Γ pointGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both sourceMatrix.encode (both firstBijection.encode (member 42 33))) := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  exact .mp hp (.mp (Context.conjunctionRight (Context.conjunctionRight hg'))
    (.mp (Context.conjunctionLeft (Context.conjunctionRight hg'))
      (.mp (Context.conjunctionLeft hg') (.closed reconstruct))))

/-- The chosen source output32, factor coordinates30/31, and target33 are
shared by the reverse and forward witnesses. -/
def reverse_point_exists : KDerivation (imp sourceMatrix.encode (imp firstBijection.encode
    (imp (member 42 33) (existsCode 32 (existsCode 30 (existsCode 31 reconstructed.encode)))))) := by
  have h31 := conditionalExistsCongr 31 (free_vacuity 31 pointGuard (by decide)) point_reconstruct
  have h30 := conditionalExistsCongr 30 (free_vacuity 30 pointGuard (by decide)) h31
  have h32 := conditionalExistsCongr 32 (free_vacuity 32 pointGuard (by decide)) h30
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 42 33,firstBijection.encode,sourceMatrix.encode]
  have hy : Context Γ (member 42 33) := .head _ _
  have hb : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ sourceMatrix.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ pointGuard.encode := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hm (Context.conjunctionIntro hb hy)
  have hp := Context.mp hy (Context.mp hb (Context.mp hm (.closed paired_preimage_exists)))
  exact .mp hp (.mp hg (.closed h32))

theorem reverse_point_exists_certificate : theoremCode (certificate reverse_point_exists) =
    imp sourceMatrix.encode (imp firstBijection.encode (imp (member 42 33)
      (existsCode 32 (existsCode 30 (existsCode 31 reconstructed.encode))))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputReversePoint

#print axioms PASoundness.PAtoCompactProductOutputReversePoint.point_reconstruct
#print axioms PASoundness.PAtoCompactProductOutputReversePoint.reverse_point_exists
#print axioms PASoundness.PAtoCompactProductOutputReversePoint.reverse_point_exists_certificate
