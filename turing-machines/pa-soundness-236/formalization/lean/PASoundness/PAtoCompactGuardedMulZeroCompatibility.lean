import PASoundness.PAtoCompactGuardedAdditionCompatibility
import PASoundness.PAtoCompactMulZeroAxiomAllTerms

/-! Compose the constructed guarded multiplication-by-zero axiom with the
existing checked PA-to-K compiler. Occurrence-conditioned substitution
compatibility, guarded equality substitution, and the multiplication-successor
axiom family remain explicit finite K proof-data inputs. This noncomputable
proof transformation is not an executable proof extractor. -/

namespace PASoundness.PAtoCompactGuardedMulZeroCompatibility

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The multiplication-successor axiom proof family, retained explicitly. -/
abbrev MulSuccHandler := ∀ t u : Peano.Term,
  KDerivation (guardedCode ((Peano.mul t (Peano.succ u)).equal (Peano.add (Peano.mul t u) t)))

/-- Supply the constructed multiplication-by-zero proof and retain the
multiplication-successor proof family. -/
noncomputable def withMulZero (mulSucc : MulSuccHandler) :
    PAtoCompactGuardedAdditionBridge.RemainingArithmetic where
  mulZero := PAtoCompactMulZeroAxiomAllTerms.mul_zero
  mulSucc := mulSucc

theorem multiplication_zero_certificate (mulSucc : MulSuccHandler) (t : Peano.Term) :
    theoremCode (certificate ((withMulZero mulSucc).mulZero t)) =
      guardedCode ((Peano.mul t Peano.zero).equal Peano.zero) := certificate_correct _

/-- Assemble the guarded compiler under the displayed occurrence-conditioned
compatibility, equality-substitution, and multiplication-successor inputs. -/
noncomputable def handlers
    (logical : PAtoCompactGuardedCompatibilityBridge.CompatibilityInputs)
    (mulSucc : MulSuccHandler) : PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedAdditionCompatibility.handlers logical (withMulZero mulSucc)

/-- Translate a checked PA proof certificate under the displayed remaining
logical and multiplication-successor proof inputs. -/
noncomputable def translateChecked
    (logical : PAtoCompactGuardedCompatibilityBridge.CompatibilityInputs)
    (mulSucc : MulSuccHandler) (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PAtoCompactGuardedBridge.translateChecked (handlers logical mulSucc) c φ hc

theorem translated_certificate
    (logical : PAtoCompactGuardedCompatibilityBridge.CompatibilityInputs)
    (mulSucc : MulSuccHandler) (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked logical mulSucc c φ hc)) = guardedCode φ :=
  certificate_correct _

/-- Literal machine acceptance is equivalent to PA soundness under the
displayed compatibility, equality-substitution and multiplication-successor
proof inputs. -/
theorem selected_accepts_iff_pa_soundness
    (logical : PAtoCompactGuardedCompatibilityBridge.CompatibilityInputs)
    (mulSucc : MulSuccHandler) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness (handlers logical mulSucc)

end PASoundness.PAtoCompactGuardedMulZeroCompatibility

#print axioms PASoundness.PAtoCompactGuardedMulZeroCompatibility.MulSuccHandler
#print axioms PASoundness.PAtoCompactGuardedMulZeroCompatibility.withMulZero
#print axioms PASoundness.PAtoCompactGuardedMulZeroCompatibility.multiplication_zero_certificate
#print axioms PASoundness.PAtoCompactGuardedMulZeroCompatibility.handlers
#print axioms PASoundness.PAtoCompactGuardedMulZeroCompatibility.translateChecked
#print axioms PASoundness.PAtoCompactGuardedMulZeroCompatibility.translated_certificate
#print axioms PASoundness.PAtoCompactGuardedMulZeroCompatibility.selected_accepts_iff_pa_soundness
