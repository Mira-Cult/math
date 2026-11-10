import PASoundness.PAtoCompactGuardedInductionSuccBridge
import PASoundness.PAtoCompactSuccInjectivityProofClosed

/-! Assemble the guarded PA-to-K compiler using the constructed induction,
successor-not-zero and successor-injectivity handlers. The four addition and
multiplication axiom families and the three logical axiom families remain
explicit finite K proof-data inputs. This is not an executable proof extractor. -/

namespace PASoundness.PAtoCompactGuardedSuccessorBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The four arithmetic proof handlers remaining after induction and both
successor axiom families have been constructed. -/
structure RemainingArithmetic where
  addZero : ∀ t : Peano.Term,
    KDerivation (guardedCode ((Peano.add t Peano.zero).equal t))
  addSucc : ∀ t u : Peano.Term,
    KDerivation (guardedCode ((Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))))
  mulZero : ∀ t : Peano.Term,
    KDerivation (guardedCode ((Peano.mul t Peano.zero).equal Peano.zero))
  mulSucc : ∀ t u : Peano.Term,
    KDerivation (guardedCode ((Peano.mul t (Peano.succ u)).equal (Peano.add (Peano.mul t u) t)))

/-- Supply the constructed successor-injectivity proof and retain the four
addition and multiplication handlers. -/
noncomputable def withSuccessorInjectivity (h : RemainingArithmetic) :
    PAtoCompactGuardedInductionSuccBridge.RemainingArithmetic where
  succInjective := PAtoCompactSuccInjectivityProofClosed.guarded_successor_injective
  addZero := h.addZero
  addSucc := h.addSucc
  mulZero := h.mulZero
  mulSucc := h.mulSucc

theorem successor_injectivity_certificate (h : RemainingArithmetic) (t u : Peano.Term) :
    theoremCode (certificate ((withSuccessorInjectivity h).succInjective t u)) =
      guardedCode (((Peano.succ t).equal (Peano.succ u)).imp (t.equal u)) :=
  certificate_correct _

/-- Assemble the guarded compiler with the three proved axiom handlers. -/
noncomputable def handlers (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : RemainingArithmetic) : PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedInductionSuccBridge.handlers logical (withSuccessorInjectivity arithmetic)

/-- Translate an actual checked PA certificate to finite K proof data under
the displayed logical and addition/multiplication handlers. -/
noncomputable def translateChecked (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : RemainingArithmetic) (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PAtoCompactGuardedBridge.translateChecked (handlers logical arithmetic) c φ hc

theorem translated_certificate (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : RemainingArithmetic) (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked logical arithmetic c φ hc)) = guardedCode φ :=
  certificate_correct _

/-- Literal machine acceptance is equivalent to PA soundness under the
displayed three logical and four remaining arithmetic handlers. -/
theorem selected_accepts_iff_pa_soundness
    (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : RemainingArithmetic) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness (handlers logical arithmetic)

end PASoundness.PAtoCompactGuardedSuccessorBridge

#print axioms PASoundness.PAtoCompactGuardedSuccessorBridge.RemainingArithmetic
#print axioms PASoundness.PAtoCompactGuardedSuccessorBridge.withSuccessorInjectivity
#print axioms PASoundness.PAtoCompactGuardedSuccessorBridge.successor_injectivity_certificate
#print axioms PASoundness.PAtoCompactGuardedSuccessorBridge.handlers
#print axioms PASoundness.PAtoCompactGuardedSuccessorBridge.translateChecked
#print axioms PASoundness.PAtoCompactGuardedSuccessorBridge.translated_certificate
#print axioms PASoundness.PAtoCompactGuardedSuccessorBridge.selected_accepts_iff_pa_soundness
