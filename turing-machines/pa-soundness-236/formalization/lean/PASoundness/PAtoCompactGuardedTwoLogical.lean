import PASoundness.PAtoCompactGuardedDirectBridge
import PASoundness.PAtoCompactGuardedEqualityReflexivityClosed

/-! Supply the proved guarded equality-reflexivity family to the direct
PA-to-K compiler. Universal elimination, equality substitution, and all PA
axioms including induction remain explicit finite-K-proof inputs. The proof
transformer is noncomputable and is not an executable proof extractor. -/
namespace PASoundness.PAtoCompactGuardedTwoLogical

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The two logical axiom families still needed by the guarded compiler. -/
structure TwoLogical where
  allElim : ∀ (φ : Peano.Formula) (x : Nat) (t : Peano.Term),
    KDerivation (guardedCode ((FOL.allAt x φ).imp (FOL.substAt φ x t)))
  eqSubst : ∀ (φ : Peano.Formula) (x : Nat) (t u : Peano.Term),
    KDerivation (guardedCode ((t.equal u).imp ((FOL.substAt φ x t).imp (FOL.substAt φ x u))))

/-- Supply guarded reflexivity for every PA term using the finite K proof
constructed from term-graph existence. -/
noncomputable def threeLogical (logical : TwoLogical) :
    PAtoCompactGuardedThreeLogical.ThreeLogical where
  allElim := logical.allElim
  eqRefl := PAtoCompactGuardedEqualityReflexivityClosed.reflexivity
  eqSubst := logical.eqSubst

/-- Build the existing compiler handlers. The two logical families and the
full PA-axiom handler remain explicit inputs. -/
noncomputable def handlers (logical : TwoLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)) :
    PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedDirectBridge.handlers (threeLogical logical) arithmetic

/-- Translate an actual checked PA proof certificate to finite K proof data
under the two remaining logical-family handlers and full PA-axiom handler. -/
noncomputable def translateChecked (logical : TwoLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ))
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PAtoCompactGuardedBridge.translateChecked (handlers logical arithmetic) c φ hc

theorem translated_certificate (logical : TwoLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ))
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked logical arithmetic c φ hc)) = guardedCode φ :=
  certificate_correct _

/-- Literal machine acceptance is equivalent to PA soundness conditional on
the displayed two logical-family handlers and full PA-axiom handler. -/
theorem selected_accepts_iff_pa_soundness
    (logical : TwoLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedDirectBridge.selected_accepts_iff_pa_soundness (threeLogical logical) arithmetic

end PASoundness.PAtoCompactGuardedTwoLogical

#print axioms PASoundness.PAtoCompactGuardedTwoLogical.threeLogical
#print axioms PASoundness.PAtoCompactGuardedTwoLogical.handlers
#print axioms PASoundness.PAtoCompactGuardedTwoLogical.translateChecked
#print axioms PASoundness.PAtoCompactGuardedTwoLogical.translated_certificate
#print axioms PASoundness.PAtoCompactGuardedTwoLogical.selected_accepts_iff_pa_soundness
