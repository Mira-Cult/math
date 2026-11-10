import PASoundness.PeanoClosedToOpenSoundness
import PASoundness.PeanoPowerGrowth
import PASoundness.M236MachineCompact

/-! A conditional PA-to-machine direction, using explicit proof transport
and standard-truth preservation, not independently proved soundness. -/
namespace PASoundness.PASoundnessToM236
open FirstOrder FirstOrder.Language
open Peano CompactArithmetic CompactLogicalTransport
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- Assuming closed-sentence PA soundness and explicit PA derivations of
the guarded comprehension family, each compact proof is true at every
assignment. The proof transports the actual derivation into PA and applies
the standard-model truth correspondence for that translated formula. -/
theorem compact_sound_of_pa_soundness
    (hPA : ∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s)
    (hcomprehension : ∀ a b c, c ≠ a → c ≠ b →
      Peano.FormulaProves (comprehensionFormula a b c)) :
    M236Reverse.CompactSound := by
  intro f d ρ
  have hproof : Peano.FormulaProves (interpreted f) :=
    derivation_transport_from_comprehension PeanoPowerGrowth.translated_bottom
      hcomprehension d
  have htrue : (interpreted f).Realize ρ :=
    PeanoClosedToOpenSoundness.open_of_closed_soundness hPA (interpreted f) hproof ρ
  exact (CompactArithmetic.realize_translate (CompactMatrix.decode f) ρ).mp htrue

/-- The same hypotheses imply guarded ω-acceptance of the literal selected
blank-start machine. Comprehension derivations remain an explicit premise;
the reverse PA bridge is not asserted. -/
theorem selected_accepts_of_pa_soundness
    (hPA : ∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s)
    (hcomprehension : ∀ a b c, c ≠ a → c ≠ b →
      Peano.FormulaProves (comprehensionFormula a b c)) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) :=
  M236MachineCompact.selected_trace_iff_compact_sound.mpr
    (compact_sound_of_pa_soundness hPA hcomprehension)

end PASoundness.PASoundnessToM236

#print axioms PASoundness.PASoundnessToM236.compact_sound_of_pa_soundness
#print axioms PASoundness.PASoundnessToM236.selected_accepts_of_pa_soundness
