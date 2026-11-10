import PASoundness.PASoundnessToM236
import PASoundness.PeanoAX8Comprehension

/-! Discharge the arithmetic proof-translation premise in the PA-to-machine
direction by the explicit guarded PA comprehension derivations. -/
namespace PASoundness.PASoundnessToM236Closed
open FirstOrder FirstOrder.Language
open Peano CompactArithmetic CompactLogicalTransport
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- Genuine closed-sentence PA soundness implies compact-calculus soundness
through the constructed PA proof translation and its truth correspondence. -/
theorem compact_sound_of_pa_soundness
    (hPA : ∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :
    M236Reverse.CompactSound :=
  PASoundnessToM236.compact_sound_of_pa_soundness hPA PeanoAX8Comprehension.comprehension

/-- Genuine PA soundness implies guarded ω-acceptance of the literal selected
blank-start machine. This proves only the indicated direction. -/
theorem selected_accepts_of_pa_soundness
    (hPA : ∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) :=
  PASoundnessToM236.selected_accepts_of_pa_soundness hPA PeanoAX8Comprehension.comprehension

end PASoundness.PASoundnessToM236Closed

#print axioms PASoundness.PASoundnessToM236Closed.compact_sound_of_pa_soundness
#print axioms PASoundness.PASoundnessToM236Closed.selected_accepts_of_pa_soundness
