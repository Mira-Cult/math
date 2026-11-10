import PASoundness.Certificates
import PASoundness.CompactProof

/-!
# Conditional translation of checked PA proofs to finite K proofs

This module is purely syntactic. It takes an explicit formula-code map and
finite K derivations of every translated logical and PA axiom instance, together
with implication compatibility and a generalization bridge. In particular,
the PA axiom input includes the full induction schema. None of these inputs is
constructed here; no quotient interpretation or truth-preservation claim is
made. The transformer consumes the existing checked PA proof tree, rather than
extracting data by eliminating a Prop-valued derivation into Type.
-/

namespace PASoundness.PAtoCompactParametricProof

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof

/-- The still-open, explicit obligations for a formula translation. The
logical and arithmetic handlers accept exactly the repository's decoders;
the latter includes every instance of induction, including parameters. -/
structure Translation where
  code : Peano.Formula → Nat
  implication : ∀ φ ψ, code (φ.imp ψ) = imp (code φ) (code ψ)
  logical : ∀ c φ, Certificates.logicalDecode c = some φ → KDerivation (code φ)
  arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (code φ)
  generalization : ∀ x φ,
    KDerivation (imp (allCode x (code φ)) (code (FOL.allAt x φ)))

/-- Transform a supplied, successfully checked PA proof tree into actual
finite K proof data. This recursion uses only the supplied syntactic handlers. -/
def translateChecked (T : Translation) (c : Certificates.PAProofCode)
    (φ : Peano.Formula) (h : Certificates.paCheck c = some φ) : KDerivation (T.code φ) := by
  cases c with
  | logical c => exact T.logical c φ h
  | nonlogical c => exact T.arithmetic c φ h
  | generalize x c =>
      cases hc : Certificates.check Certificates.paDecode c with
      | none => simp [Certificates.paCheck, Certificates.check, hc] at h
      | some ψ =>
          simp only [Certificates.paCheck, Certificates.check, hc, Option.map_some,
            Option.some.injEq] at h
          subst φ
          exact .mp (.generalize x (translateChecked T c ψ hc)) (T.generalization x ψ)
  | mp p q =>
      cases hp : Certificates.check Certificates.paDecode p with
      | none => simp [Certificates.paCheck, Certificates.check, hp] at h
      | some ψ =>
          cases ψ with
          | falsum => simp [Certificates.paCheck, Certificates.check, hp] at h
          | equal _ _ => simp [Certificates.paCheck, Certificates.check, hp] at h
          | rel _ _ => simp [Certificates.paCheck, Certificates.check, hp] at h
          | all _ => simp [Certificates.paCheck, Certificates.check, hp] at h
          | imp a b =>
              cases hq : Certificates.check Certificates.paDecode q with
              | none => simp [Certificates.paCheck, Certificates.check, hp, hq] at h
              | some χ =>
                  by_cases he : a = χ
                  · subst χ
                    simp [Certificates.paCheck, Certificates.check, hp, hq] at h
                    subst φ
                    have hp' : KDerivation (imp (T.code a) (T.code b)) := by
                      rw [← T.implication]
                      exact translateChecked T p _ hp
                    exact .mp (translateChecked T q _ hq) hp'
                  · simp [Certificates.paCheck, Certificates.check, hp, hq, he] at h
termination_by c

/-- The concrete output tree is serializable as an accepted K certificate. -/
theorem translated_certificate (T : Translation) (c : Certificates.PAProofCode)
    (φ : Peano.Formula) (h : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked T c φ h)) = T.code φ :=
  certificate_correct _

/-- Ordinary PA provability gives K provability conditionally. This is a
Prop-valued existence result: it does not claim to compute a PA certificate
from an erased `FormulaProves` proof. -/
theorem transport (T : Translation) {φ : Peano.Formula}
    (h : Peano.FormulaProves φ) : KProves (T.code φ) := by
  obtain ⟨c, hc⟩ := Certificates.paCheck_complete h
  exact ⟨translateChecked T c φ hc⟩

end PASoundness.PAtoCompactParametricProof
