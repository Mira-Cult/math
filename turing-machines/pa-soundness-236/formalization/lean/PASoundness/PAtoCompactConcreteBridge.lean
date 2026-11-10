import PASoundness.PAtoCompactFormulaFullTruth
import PASoundness.PAtoCompactParametricProof
import PASoundness.M236MachineCompact
import PASoundness.PASoundnessToM236Closed

/-! Conditional reverse bridge using the concrete PA formula translation.
The handlers for translated logical and PA axioms, including induction, and
the generalization rule remain explicit proof-data inputs. No soundness
theorem is used as a replacement for these inputs. The unguarded handler
interface is in fact uninhabitable; see the separate standard-HF diagnostic
in `PAtoCompactOpenAxiomCounterexample`. A guarded proof translation or a
different representation total on raw HF values could repair the interface. -/
namespace PASoundness.PAtoCompactConcreteBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactFormulaFullTruth PASoundness.PAtoCompactParametricProof
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- Remaining K proof obligations for the actual concrete formula code.
The arithmetic handler includes the full parameterized PA induction schema. -/
structure Handlers where
  logical : ∀ c φ, Certificates.logicalDecode c = some φ → KDerivation (code φ)
  arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (code φ)
  generalization : ∀ x φ, KDerivation (imp (allCode x (code φ)) (code (FOL.allAt x φ)))

/-- The existing certificate compiler instantiated with the concrete code. -/
def translation (h : Handlers) : Translation where
  code := code
  implication := code_imp
  logical := h.logical
  arithmetic := h.arithmetic
  generalization := h.generalization

/-- A supplied checked PA certificate is transformed to actual K proof data. -/
def compileChecked (h : Handlers) (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (code φ) :=
  translateChecked (translation h) c φ hc

/-- Compact soundness transfers to the truth of an arbitrary PA theorem
through the explicit certificate compiler and formula truth correspondence. -/
theorem pa_formula_of_compact_sound (h : Handlers) (hs : M236Reverse.CompactSound)
    {φ : Peano.Formula} (hp : Peano.FormulaProves φ) (v : Nat → Nat) : φ.Realize v := by
  obtain ⟨d⟩ := transport (translation h) hp
  apply (formula_truth φ v).mp
  exact hs (code φ) d (PASoundness.PAtoCompactOpenScope.ordinalAssignment v)

/-- The literal machine's acceptance implies genuine PA sentence soundness,
conditional on the displayed K handlers. -/
theorem pa_soundness_of_selected_accepts (h : Handlers)
    (ha : TraceAccept (machineWordSystem M236.machine M236.machineLabels))
    (s : Peano.Sentence) (hp : Peano.Proves s) : Nat ⊨ s := by
  have hs := M236MachineCompact.selected_trace_iff_compact_sound.mp ha
  apply (FOL.realize_openSentence s (fun _ => 0)).mp
  exact pa_formula_of_compact_sound h hs hp (fun _ => 0)

/-- An end-to-end equivalence conditional only on the displayed K proof
handlers. Their construction is not asserted by this theorem. -/
theorem selected_accepts_iff_pa_soundness (h : Handlers) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) := by
  constructor
  · intro ha s hp
    exact pa_soundness_of_selected_accepts h ha s hp
  · exact PASoundnessToM236Closed.selected_accepts_of_pa_soundness

end PASoundness.PAtoCompactConcreteBridge

#print axioms PASoundness.PAtoCompactConcreteBridge.compileChecked
#print axioms PASoundness.PAtoCompactConcreteBridge.pa_formula_of_compact_sound
#print axioms PASoundness.PAtoCompactConcreteBridge.pa_soundness_of_selected_accepts
#print axioms PASoundness.PAtoCompactConcreteBridge.selected_accepts_iff_pa_soundness
