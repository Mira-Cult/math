import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! High-end FT block using the certified base and active pruning. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def finiteTwinHigh16384Widths : List ℕ := List.replicate 4 4096

theorem finiteTwinHighActive16384_checked :
    activeStreamingTwinScan finiteTwinCheckedBase 1073709055 finiteTwinHigh16384Widths = 90 := by
  decide +kernel

theorem finiteTwinHighActive16384_mathematical :
    (twinPrimeSegment 1073709055 1073741823).card = 90 := by
  have hstream := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1073709055 finiteTwinHigh16384Widths).symm.trans
    finiteTwinHighActive16384_checked
  have hscan := (streamingTwinScan_eq finiteTwinCheckedBase 1073709055 finiteTwinHigh16384Widths).symm.trans hstream
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1073709055 finiteTwinHigh16384Widths
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hscan] at h
  simpa [finiteTwinHigh16384Widths] using h.symm

end
end Sude
