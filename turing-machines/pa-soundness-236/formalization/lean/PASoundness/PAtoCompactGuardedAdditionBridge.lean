import PASoundness.PAtoCompactGuardedSuccessorBridge
import PASoundness.PAtoCompactPAAddZeroAllTerms
import PASoundness.PAtoCompactPAAddSuccAllTerms

/-! Assemble the guarded PA-to-K compiler using the constructed induction,
successor and addition axiom handlers. The two multiplication axiom families
and three logical axiom families remain explicit finite K proof-data inputs.
This noncomputable proof transformation is not an executable extractor. -/

namespace PASoundness.PAtoCompactGuardedAdditionBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The two arithmetic proof handlers remaining after induction, successor,
and addition axiom families have been constructed. -/
structure RemainingArithmetic where
  mulZero : ∀ t : Peano.Term,
    KDerivation (guardedCode ((Peano.mul t Peano.zero).equal Peano.zero))
  mulSucc : ∀ t u : Peano.Term,
    KDerivation (guardedCode ((Peano.mul t (Peano.succ u)).equal (Peano.add (Peano.mul t u) t)))

/-- Supply the constructed addition axiom proofs, retaining the two
multiplication proof families as explicit inputs. -/
noncomputable def withAddition (h : RemainingArithmetic) :
    PAtoCompactGuardedSuccessorBridge.RemainingArithmetic where
  addZero := PAtoCompactPAAddZeroAllTerms.add_zero
  addSucc := PAtoCompactPAAddSuccAllTerms.add_succ
  mulZero := h.mulZero
  mulSucc := h.mulSucc

theorem addition_zero_certificate (h : RemainingArithmetic) (t : Peano.Term) :
    theoremCode (certificate ((withAddition h).addZero t)) =
      guardedCode ((Peano.add t Peano.zero).equal t) := certificate_correct _

theorem addition_successor_certificate (h : RemainingArithmetic) (t u : Peano.Term) :
    theoremCode (certificate ((withAddition h).addSucc t u)) =
      guardedCode ((Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))) :=
  certificate_correct _

/-- Assemble the guarded compiler using the constructed induction,
successor, and addition handlers. -/
noncomputable def handlers (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : RemainingArithmetic) : PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedSuccessorBridge.handlers logical (withAddition arithmetic)

/-- Translate an actual checked PA certificate to finite K proof data under
the displayed logical and multiplication axiom handlers. -/
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
displayed three logical and two multiplication axiom handlers. -/
theorem selected_accepts_iff_pa_soundness
    (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : RemainingArithmetic) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness (handlers logical arithmetic)

end PASoundness.PAtoCompactGuardedAdditionBridge

#print axioms PASoundness.PAtoCompactGuardedAdditionBridge.RemainingArithmetic
#print axioms PASoundness.PAtoCompactGuardedAdditionBridge.withAddition
#print axioms PASoundness.PAtoCompactGuardedAdditionBridge.addition_zero_certificate
#print axioms PASoundness.PAtoCompactGuardedAdditionBridge.addition_successor_certificate
#print axioms PASoundness.PAtoCompactGuardedAdditionBridge.handlers
#print axioms PASoundness.PAtoCompactGuardedAdditionBridge.translateChecked
#print axioms PASoundness.PAtoCompactGuardedAdditionBridge.translated_certificate
#print axioms PASoundness.PAtoCompactGuardedAdditionBridge.selected_accepts_iff_pa_soundness
