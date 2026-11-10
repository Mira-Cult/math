import PASoundness.PAtoCompactGuardedTwoLogical
import PASoundness.PAtoCompactAllTermsAllElimWithTotality

/-! Refine the direct guarded PA-to-K compiler interface. Term-graph
existence and guarded reflexivity are supplied by finite K constructions.
Universal elimination still requires the displayed occurrence-conditioned
K substitution compatibility. Equality substitution and every PA axiom,
including induction, remain explicit finite-K-proof inputs. The resulting
proof transformation is noncomputable, not an executable proof extractor. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGuardedCompatibilityBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedAllElim PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactFormulaTranslation
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- Remaining K-level substitution compatibility and equality-substitution
axiom proofs. The compatibility proof is required only if the eliminated
variable actually occurs free in the source formula. -/
structure CompatibilityInputs where
  substitution : ∀ (φ : Peano.Formula) (x : Nat) (t : Peano.Term),
    x ∈ φ.freeVarFinset → KDerivation (imp
      (guardFormula (allElimFormula φ x t)).encode
      (imp (termGraph id t (outputName (allElimFormula φ x t))
        (allocatorBase (allElimFormula φ x t))).encode
        (imp (instanceBody φ x (outputName (allElimFormula φ x t))).encode
          (code (FOL.substAt φ x t)))))
  eqSubst : ∀ (φ : Peano.Formula) (x : Nat) (t u : Peano.Term),
    KDerivation (guardedCode ((t.equal u).imp ((FOL.substAt φ x t).imp (FOL.substAt φ x u))))

/-- Fill universal elimination using the proved graph witness constructor and
the explicitly supplied occurrence-conditioned compatibility family. -/
noncomputable def twoLogical (input : CompatibilityInputs) :
    PAtoCompactGuardedTwoLogical.TwoLogical where
  allElim := fun φ x t => by
    simpa only [allElimFormula] using
      (PAtoCompactAllTermsAllElimWithTotality.allElim φ x t (input.substitution φ x t))
  eqSubst := input.eqSubst

/-- Complete the direct compiler handlers from the displayed compatibility,
equality-substitution, and full PA-axiom proof inputs. -/
noncomputable def handlers (input : CompatibilityInputs)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)) :
    PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedTwoLogical.handlers (twoLogical input) arithmetic

/-- Translate an actual checked PA proof certificate to finite K proof data
under the displayed inputs. -/
noncomputable def translateChecked (input : CompatibilityInputs)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ))
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PAtoCompactGuardedBridge.translateChecked (handlers input arithmetic) c φ hc

theorem translated_certificate (input : CompatibilityInputs)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ))
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked input arithmetic c φ hc)) = guardedCode φ :=
  certificate_correct _

/-- Literal machine acceptance is equivalent to PA soundness conditional on
the displayed compatibility, equality-substitution and PA-axiom handlers. -/
theorem selected_accepts_iff_pa_soundness
    (input : CompatibilityInputs)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedTwoLogical.selected_accepts_iff_pa_soundness (twoLogical input) arithmetic
end PASoundness.PAtoCompactGuardedCompatibilityBridge

#print axioms PASoundness.PAtoCompactGuardedCompatibilityBridge.twoLogical
#print axioms PASoundness.PAtoCompactGuardedCompatibilityBridge.handlers
#print axioms PASoundness.PAtoCompactGuardedCompatibilityBridge.translateChecked
#print axioms PASoundness.PAtoCompactGuardedCompatibilityBridge.translated_certificate
#print axioms PASoundness.PAtoCompactGuardedCompatibilityBridge.selected_accepts_iff_pa_soundness
