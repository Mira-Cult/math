import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116391981 116424749 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 116391981 116424749).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116391981 116424749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116424749 116457517 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 116424749 116457517).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116424749 116457517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116457517 116490285 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 116457517 116490285).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116457517 116490285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116490285 116523053 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 116490285 116523053).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116490285 116523053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 116391981 116457517).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 116391981 ≤ 116424749)
    (by decide : 116424749 ≤ 116457517) block0 block1

theorem join_0_1 : (twinPrimeSegment 116457517 116523053).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 116457517 ≤ 116490285)
    (by decide : 116490285 ≤ 116523053) block2 block3

theorem join_1_0 : (twinPrimeSegment 116391981 116523053).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 116391981 ≤ 116457517)
    (by decide : 116457517 ≤ 116523053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 116391981 116523053).card = 473 := join_1_0

end S055C08
end Sude.GeneratedTwinScan
