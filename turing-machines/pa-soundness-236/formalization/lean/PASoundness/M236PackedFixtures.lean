import PASoundness.M236RuntimeBase

/-! Controls for the packed checker's boundaries and event accounting. -/
set_option maxRecDepth 8192
namespace PASoundness.M236.PackedFixtures
open Shared.Beeping.Machines PASoundness.M236.PackedTape

def rightRun : Configuration 237 :=
  ⟨1, 0, ⟨[], [.pair true false 1909, .bit true]⟩⟩

example : sweepRight raw rawLabels 1909 rightRun =
    some ⟨1, 3818, ⟨[.pair false true 1909], [.pair true false 0, .bit true]⟩⟩ := by decide

example : sweepRight raw rawLabels 1910 rightRun = none := by decide
example : sweepRight raw rawLabels 0 rightRun = none := by decide
example : sweepLeft raw rawLabels 1 rightRun = none := by decide
example : sweepRight raw GenericSweep.markedControl 1 rightRun = none := by decide

def marked : Configuration 237 := ⟨135, 0, ⟨[], [.bit false]⟩⟩
example : (step raw rawLabels marked).2 = [true] := by decide
example : (step raw rawLabels marked).2 ≠ [] := by decide
def markedZero : Configuration 237 := ⟨138, 0, ⟨[], [.bit true]⟩⟩
example : (step raw rawLabels markedZero).2 = [false] := by decide

end PASoundness.M236.PackedFixtures
