import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75759661 75792429 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 75759661 75792429).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75759661 75792429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75792429 75825197 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 75792429 75825197).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75792429 75825197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75825197 75857965 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 75825197 75857965).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75825197 75857965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75857965 75890733 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 75857965 75890733).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75857965 75890733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 75759661 75825197).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 75759661 ≤ 75792429)
    (by decide : 75792429 ≤ 75825197) block0 block1

theorem join_0_1 : (twinPrimeSegment 75825197 75890733).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 75825197 ≤ 75857965)
    (by decide : 75857965 ≤ 75890733) block2 block3

theorem join_1_0 : (twinPrimeSegment 75759661 75890733).card = 528 := by
  simpa using combineTwinPrimeSegments (by decide : 75759661 ≤ 75825197)
    (by decide : 75825197 ≤ 75890733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 75759661 75890733).card = 528 := join_1_0

end S036C02
end Sude.GeneratedTwinScan
