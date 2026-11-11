import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118489133 118521901 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 118489133 118521901).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118489133 118521901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118521901 118554669 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 118521901 118554669).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118521901 118554669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118554669 118587437 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 118554669 118587437).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118554669 118587437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118587437 118620205 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 118587437 118620205).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118587437 118620205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 118489133 118554669).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 118489133 ≤ 118521901)
    (by decide : 118521901 ≤ 118554669) block0 block1

theorem join_0_1 : (twinPrimeSegment 118554669 118620205).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 118554669 ≤ 118587437)
    (by decide : 118587437 ≤ 118620205) block2 block3

theorem join_1_0 : (twinPrimeSegment 118489133 118620205).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 118489133 ≤ 118554669)
    (by decide : 118554669 ≤ 118620205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 118489133 118620205).card = 490 := join_1_0

end S056C08
end Sude.GeneratedTwinScan
