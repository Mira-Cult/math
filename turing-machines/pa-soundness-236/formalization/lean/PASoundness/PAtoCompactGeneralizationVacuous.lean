import PASoundness.PAtoCompactGeneralizationFreshAlpha
import PASoundness.PAtoCompactGuardedVacuity
import PASoundness.PAtoCompactGuardedGeneralizationAlignment
import PASoundness.PAtoCompactGuardedModusPonens
import PASoundness.PAtoCompactGuardedVacuousAxiom

/-! A conditional guarded generalization step when the generalized source
name is absent. The remaining premise is actual K proof data aligning the
capture-safe freshened body with the separately generated body. -/
namespace PASoundness.PAtoCompactGeneralizationVacuous

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedVacuity PASoundness.PAtoCompactGuardedModusPonens
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactGeneralizationFreshAlpha
open PASoundness.PAtoCompactGuardedVacuousAxiom PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactTermTranslation

/-- A freshened-body alignment suffices to generalize an already guarded
proof when the source variable is not free. This does not construct the
alignment and is not the unrestricted generalization handler. -/
def generalize_of_body_alignment (φ : Peano.Formula) (x start : Nat)
    (hx : x ∉ φ.freeVarFinset)
    (hn : ∀ v ∈ (formula φ).names, v < start)
    (hxs : x < start) (hzs : topName x φ < start)
    (halign : KDerivation (imp
      (replace x (topName x φ) (freshen (formula φ) start hn).formula).encode
      (topBody x φ).encode))
    (d : KDerivation (guardedCode φ)) : KDerivation (guardedCode (FOL.allAt x φ)) := by
  have hguard : guardFormula (FOL.allAt x φ) = guardFormula φ := by
    apply guard_eq_of_free_eq
    simp [PASoundness.SyntaxTransport.allAt_freeVars, hx]
  have halpha : ProofEquiv (.all x (formula φ))
      (.all (topName x φ) (replace x (topName x φ) (freshen (formula φ) start hn).formula)) := by
    by_cases he : x = topName x φ
    · rw [← he]
      exact universal_fresh_same (formula φ) start x hn
    · apply universal_fresh_alpha (formula φ) start x (topName x φ) hn hxs hzs he
      intro hm
      exact topName_not_free φ x hx (formula_free_subset φ hm)
  have hb : KDerivation (imp
      (replace x (topName x φ) (freshen (formula φ) start hn).formula).encode
      (imp (domainAt (topName x φ + 1) (topName x φ)).encode (topBody x φ).encode)) :=
    compose halign (weakening _ _)
  have hc := compose (generalize_guarded_body φ x hx d)
    (compose halpha.forward (allCongr (topName x φ) hb))
  simpa only [guardedCode, hguard, code_allAt] using hc

theorem generalize_of_body_alignment_certificate (φ : Peano.Formula) (x start : Nat)
    (hx : x ∉ φ.freeVarFinset)
    (hn : ∀ v ∈ (formula φ).names, v < start)
    (hxs : x < start) (hzs : topName x φ < start)
    (halign : KDerivation (imp
      (replace x (topName x φ) (freshen (formula φ) start hn).formula).encode
      (topBody x φ).encode))
    (d : KDerivation (guardedCode φ)) :
    theoremCode (certificate (generalize_of_body_alignment φ x start hx hn hxs hzs halign d)) =
      guardedCode (FOL.allAt x φ) := certificate_correct _

end PASoundness.PAtoCompactGeneralizationVacuous

#print axioms PASoundness.PAtoCompactGeneralizationVacuous.generalize_of_body_alignment
#print axioms PASoundness.PAtoCompactGeneralizationVacuous.generalize_of_body_alignment_certificate
