import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116523053 116555821 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 116523053 116555821).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116523053 116555821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116555821 116588589 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 116555821 116588589).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116555821 116588589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116588589 116621357 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 116588589 116621357).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116588589 116621357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116621357 116654125 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 116621357 116654125).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116621357 116654125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 116523053 116588589).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 116523053 ≤ 116555821)
    (by decide : 116555821 ≤ 116588589) block0 block1

theorem join_0_1 : (twinPrimeSegment 116588589 116654125).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 116588589 ≤ 116621357)
    (by decide : 116621357 ≤ 116654125) block2 block3

theorem join_1_0 : (twinPrimeSegment 116523053 116654125).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 116523053 ≤ 116588589)
    (by decide : 116588589 ≤ 116654125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 116523053 116654125).card = 491 := join_1_0

end S055C09
end Sude.GeneratedTwinScan
