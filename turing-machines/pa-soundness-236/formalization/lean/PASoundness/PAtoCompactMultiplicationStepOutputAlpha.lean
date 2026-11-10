import PASoundness.PAtoCompactTermTranslation

/-! Capture-safe output-binder conversion for the multiplication induction
step. This constructs finite K proof data only; it does not assert the local
successor law, multiplication totality, or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationStepOutputAlpha
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def outputBody : Formula := andF (domainAt 300 32) (mulAt 300 205 30 32)

private theorem renamed_output : replace 32 45 outputBody =
    andF (domainAt 300 45) (mulAt 300 205 30 45) := by decide

/-- Alpha-convert a candidate product witness at bound name 45 to bound
name 32, retaining both the candidate guard and the literal product graph. -/
def output_alpha : KDerivation
    (imp (existsCode 45 (andF (domainAt 300 45) (mulAt 300 205 30 45)).encode)
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 205 30 32)).encode)) := by
  have h := existentialAlpha 32 45 outputBody (by decide) (by decide) (by decide)
  rw [renamed_output] at h
  exact h.2

theorem output_alpha_certificate : theoremCode (certificate output_alpha) =
    imp (existsCode 45 (andF (domainAt 300 45) (mulAt 300 205 30 45)).encode)
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 205 30 32)).encode) :=
  certificate_correct output_alpha
end PASoundness.PAtoCompactMultiplicationStepOutputAlpha
#print axioms PASoundness.PAtoCompactMultiplicationStepOutputAlpha.output_alpha
#print axioms PASoundness.PAtoCompactMultiplicationStepOutputAlpha.output_alpha_certificate
