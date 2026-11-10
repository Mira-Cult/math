import PASoundness.PAtoCompactGuardedInductionBridge
import PASoundness.PAtoCompactSuccNeZeroAxiomClosed

/-! The guarded compiler with both induction and successor-not-zero
constructed. The five other arithmetic axiom families and three logical axiom
families remain explicit finite K proof-data inputs. This is not an executable
proof extractor. -/

namespace PASoundness.PAtoCompactGuardedInductionSuccBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The remaining PA arithmetic proof handlers after induction and
successor-not-zero have been constructed. -/
structure RemainingArithmetic where
  succInjective : ∀ t u : Peano.Term,
    KDerivation (guardedCode (((Peano.succ t).equal (Peano.succ u)).imp (t.equal u)))
  addZero : ∀ t : Peano.Term,
    KDerivation (guardedCode ((Peano.add t Peano.zero).equal t))
  addSucc : ∀ t u : Peano.Term,
    KDerivation (guardedCode ((Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))))
  mulZero : ∀ t : Peano.Term,
    KDerivation (guardedCode ((Peano.mul t Peano.zero).equal Peano.zero))
  mulSucc : ∀ t u : Peano.Term,
    KDerivation (guardedCode ((Peano.mul t (Peano.succ u)).equal (Peano.add (Peano.mul t u) t)))

/-- Fill the previously explicit successor-not-zero family with its
constructed finite K proof, retaining all five other fields verbatim. -/
noncomputable def nonInductionArithmetic (h : RemainingArithmetic) :
    PAtoCompactGuardedInductionBridge.NonInductionArithmetic where
  succNeZero := PAtoCompactSuccNeZeroAxiomClosed.succ_ne_zero
  succInjective := h.succInjective
  addZero := h.addZero
  addSucc := h.addSucc
  mulZero := h.mulZero
  mulSucc := h.mulSucc

theorem successor_not_zero_branch (h : RemainingArithmetic) (t : Peano.Term) :
    (nonInductionArithmetic h).succNeZero t =
      PAtoCompactSuccNeZeroAxiomClosed.succ_ne_zero t := rfl

/-- Assemble the guarded compiler without an induction or
successor-not-zero proof input. -/
noncomputable def handlers (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : RemainingArithmetic) : PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedInductionBridge.handlers logical (nonInductionArithmetic arithmetic)

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
displayed three logical and five remaining arithmetic handlers. -/
theorem selected_accepts_iff_pa_soundness
    (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : RemainingArithmetic) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness (handlers logical arithmetic)

end PASoundness.PAtoCompactGuardedInductionSuccBridge

#print axioms PASoundness.PAtoCompactGuardedInductionSuccBridge.RemainingArithmetic
#print axioms PASoundness.PAtoCompactGuardedInductionSuccBridge.nonInductionArithmetic
#print axioms PASoundness.PAtoCompactGuardedInductionSuccBridge.successor_not_zero_branch
#print axioms PASoundness.PAtoCompactGuardedInductionSuccBridge.handlers
#print axioms PASoundness.PAtoCompactGuardedInductionSuccBridge.translateChecked
#print axioms PASoundness.PAtoCompactGuardedInductionSuccBridge.translated_certificate
#print axioms PASoundness.PAtoCompactGuardedInductionSuccBridge.selected_accepts_iff_pa_soundness
