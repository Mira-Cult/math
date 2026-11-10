import PASoundness.PAtoCompactGuardedModusPonensFull
import PASoundness.PAtoCompactDirectGeneralization

/-! Compile checked PA proofs after a formula transformation preserving the
proof-rule connectives. The transformed logical and arithmetic axiom leaves
are explicit proof-data inputs. This is not a proof of those leaves or an
executable extractor from an erased derivability witness. -/

namespace PASoundness.PAtoCompactFormulaTransformCompiler

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge

/-- Proof data for every transformed checked axiom leaf. -/
structure TransformedLeaves (F : Peano.Formula → Peano.Formula) where
  logical : ∀ c φ, Certificates.logicalDecode c = some φ →
    KDerivation (guardedCode (F φ))
  arithmetic : ∀ c φ, Certificates.paDecode c = some φ →
    KDerivation (guardedCode (F φ))

/-- Transform a checked PA proof, given proofs for its transformed leaves
and exact preservation of implication and named universal quantification. -/
noncomputable def translateChecked (F : Peano.Formula → Peano.Formula)
    (hImp : ∀ φ ψ, F (φ.imp ψ) = (F φ).imp (F ψ))
    (hAll : ∀ x φ, F (FOL.allAt x φ) = FOL.allAt x (F φ))
    (leaves : TransformedLeaves F) (c : Certificates.PAProofCode)
    (φ : Peano.Formula) (hc : Certificates.paCheck c = some φ) :
    KDerivation (guardedCode (F φ)) := by
  cases c with
  | logical c => exact leaves.logical c φ hc
  | nonlogical c => exact leaves.arithmetic c φ hc
  | generalize x c =>
      cases hp : Certificates.check Certificates.paDecode c with
      | none => simp [Certificates.paCheck, Certificates.check, hp] at hc
      | some ψ =>
          simp only [Certificates.paCheck, Certificates.check, hp, Option.map_some,
            Option.some.injEq] at hc
          subst φ
          simpa only [hAll] using
            PAtoCompactDirectGeneralization.generalization_unconditional x (F ψ)
              (translateChecked F hImp hAll leaves c ψ hp)
  | mp p q =>
      cases hp : Certificates.check Certificates.paDecode p with
      | none => simp [Certificates.paCheck, Certificates.check, hp] at hc
      | some ψ =>
          cases ψ with
          | falsum => simp [Certificates.paCheck, Certificates.check, hp] at hc
          | equal _ _ => simp [Certificates.paCheck, Certificates.check, hp] at hc
          | rel _ _ => simp [Certificates.paCheck, Certificates.check, hp] at hc
          | all _ => simp [Certificates.paCheck, Certificates.check, hp] at hc
          | imp a b =>
              cases hq : Certificates.check Certificates.paDecode q with
              | none => simp [Certificates.paCheck, Certificates.check, hp, hq] at hc
              | some χ =>
                  by_cases he : a = χ
                  · subst χ
                    simp [Certificates.paCheck, Certificates.check, hp, hq] at hc
                    subst φ
                    exact PAtoCompactGuardedModusPonensFull.modusPonens (F a) (F b)
                      (by simpa only [hImp] using translateChecked F hImp hAll leaves p _ hp)
                      (translateChecked F hImp hAll leaves q _ hq)
                  · simp [Certificates.paCheck, Certificates.check, hp, hq, he] at hc
termination_by c

theorem translated_certificate (F : Peano.Formula → Peano.Formula)
    (hImp : ∀ φ ψ, F (φ.imp ψ) = (F φ).imp (F ψ))
    (hAll : ∀ x φ, F (FOL.allAt x φ) = FOL.allAt x (F φ))
    (leaves : TransformedLeaves F) (c : Certificates.PAProofCode)
    (φ : Peano.Formula) (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked F hImp hAll leaves c φ hc)) =
      guardedCode (F φ) := certificate_correct _

end PASoundness.PAtoCompactFormulaTransformCompiler

#print axioms PASoundness.PAtoCompactFormulaTransformCompiler.TransformedLeaves
#print axioms PASoundness.PAtoCompactFormulaTransformCompiler.translateChecked
#print axioms PASoundness.PAtoCompactFormulaTransformCompiler.translated_certificate
