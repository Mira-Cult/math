import PASoundness.PAtoCompactGuardedDirectBridge
import PASoundness.PAtoCompactFullInductionProofClosed

/-! Construct the induction branch of the guarded PA-to-K proof compiler.
The six remaining PA arithmetic axiom families and three logical axiom
families are explicit finite K proof-data inputs. This is a noncomputable
proof-data transformation, not an executable extractor. -/

namespace PASoundness.PAtoCompactGuardedInductionBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- Finite K proof handlers for the six PA axiom families other than
induction. Each field is the literal guarded translation of the corresponding
`Certificates.PACode` constructor. -/
structure NonInductionArithmetic where
  succNeZero : ∀ t : Peano.Term,
    KDerivation (guardedCode ((Peano.succ t).equal Peano.zero).not)
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

/-- Decode a PA axiom certificate into guarded K proof data. The induction
case is constructed, including for arbitrary formulas with parameters. -/
noncomputable def arithmetic (h : NonInductionArithmetic) (c : Certificates.PACode)
    (φ : Peano.Formula) (hc : Certificates.paDecode c = some φ) :
    KDerivation (guardedCode φ) := by
  cases c with
  | succNeZero t => cases hc; exact h.succNeZero t
  | succInjective t u => cases hc; exact h.succInjective t u
  | addZero t => cases hc; exact h.addZero t
  | addSucc t u => cases hc; exact h.addSucc t u
  | mulZero t => cases hc; exact h.mulZero t
  | mulSucc t u => cases hc; exact h.mulSucc t u
  | induction ψ x =>
      cases hc
      exact PAtoCompactFullInductionProofClosed.full_induction_closed ψ x

/-- The induction certificate branch uses the constructed induction proof,
independently of the six supplied non-induction handlers. -/
theorem arithmetic_induction (h : NonInductionArithmetic) (φ : Peano.Formula) (x : Nat) :
    arithmetic h (.induction φ x) (Peano.inductionAxiom φ x) rfl =
      PAtoCompactFullInductionProofClosed.full_induction_closed φ x := rfl

theorem arithmetic_certificate (h : NonInductionArithmetic) (c : Certificates.PACode)
    (φ : Peano.Formula) (hc : Certificates.paDecode c = some φ) :
    theoremCode (certificate (arithmetic h c φ hc)) = guardedCode φ := certificate_correct _

/-- The original guarded compiler interface, assembled with the proved
induction handler. -/
noncomputable def handlers (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmeticHandlers : NonInductionArithmetic) : PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedDirectBridge.handlers logical (arithmetic arithmeticHandlers)

/-- Translate an actual checked PA proof using the displayed non-induction
arithmetic handlers and three logical axiom handlers. -/
noncomputable def translateChecked (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmeticHandlers : NonInductionArithmetic)
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PAtoCompactGuardedBridge.translateChecked (handlers logical arithmeticHandlers) c φ hc

theorem translated_certificate (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmeticHandlers : NonInductionArithmetic)
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked logical arithmeticHandlers c φ hc)) = guardedCode φ :=
  certificate_correct _

/-- Literal machine acceptance is equivalent to PA soundness under the
displayed three logical and six non-induction arithmetic handlers. -/
theorem selected_accepts_iff_pa_soundness
    (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmeticHandlers : NonInductionArithmetic) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness (handlers logical arithmeticHandlers)

end PASoundness.PAtoCompactGuardedInductionBridge

#print axioms PASoundness.PAtoCompactGuardedInductionBridge.NonInductionArithmetic
#print axioms PASoundness.PAtoCompactGuardedInductionBridge.arithmetic
#print axioms PASoundness.PAtoCompactGuardedInductionBridge.arithmetic_induction
#print axioms PASoundness.PAtoCompactGuardedInductionBridge.arithmetic_certificate
#print axioms PASoundness.PAtoCompactGuardedInductionBridge.handlers
#print axioms PASoundness.PAtoCompactGuardedInductionBridge.translateChecked
#print axioms PASoundness.PAtoCompactGuardedInductionBridge.translated_certificate
#print axioms PASoundness.PAtoCompactGuardedInductionBridge.selected_accepts_iff_pa_soundness
