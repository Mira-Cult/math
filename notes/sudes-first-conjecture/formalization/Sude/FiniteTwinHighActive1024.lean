import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! High-end FT segment using the certified literal base and active pruning. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The final 1,024 candidate lower endpoints, checked with a certified base. -/
theorem finiteTwinHighActive1024_checked :
    activeStreamingTwinScan finiteTwinCheckedBase 1073739775 [1024] = 6 := by
  decide +kernel

theorem finiteTwinHighActive1024_mathematical :
    (twinPrimeSegment 1073739775 1073741823).card = 6 := by
  have hstream := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1073739775 [1024]).symm.trans
    finiteTwinHighActive1024_checked
  have hscan := (streamingTwinScan_eq finiteTwinCheckedBase 1073739775 [1024]).symm.trans hstream
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1073739775 [1024]
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hscan] at h
  simpa using h.symm

end
end Sude
