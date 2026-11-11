import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64225325 64258093 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 64225325 64258093).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64225325 64258093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64258093 64290861 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 64258093 64290861).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64258093 64290861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64290861 64323629 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 64290861 64323629).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64290861 64323629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64323629 64356397 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 64323629 64356397).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64323629 64356397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 64225325 64290861).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 64225325 ≤ 64258093)
    (by decide : 64258093 ≤ 64290861) block0 block1

theorem join_0_1 : (twinPrimeSegment 64290861 64356397).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 64290861 ≤ 64323629)
    (by decide : 64323629 ≤ 64356397) block2 block3

theorem join_1_0 : (twinPrimeSegment 64225325 64356397).card = 536 := by
  simpa using combineTwinPrimeSegments (by decide : 64225325 ≤ 64290861)
    (by decide : 64290861 ≤ 64356397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 64225325 64356397).card = 536 := join_1_0

end S030C10
end Sude.GeneratedTwinScan
