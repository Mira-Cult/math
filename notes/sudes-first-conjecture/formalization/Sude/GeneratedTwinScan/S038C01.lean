import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79822893 79855661 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 79822893 79855661).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79822893 79855661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79855661 79888429 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 79855661 79888429).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79855661 79888429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79888429 79921197 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 79888429 79921197).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79888429 79921197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79921197 79953965 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 79921197 79953965).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79921197 79953965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 79822893 79888429).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 79822893 ≤ 79855661)
    (by decide : 79855661 ≤ 79888429) block0 block1

theorem join_0_1 : (twinPrimeSegment 79888429 79953965).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 79888429 ≤ 79921197)
    (by decide : 79921197 ≤ 79953965) block2 block3

theorem join_1_0 : (twinPrimeSegment 79822893 79953965).card = 537 := by
  simpa using combineTwinPrimeSegments (by decide : 79822893 ≤ 79888429)
    (by decide : 79888429 ≤ 79953965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 79822893 79953965).card = 537 := join_1_0

end S038C01
end Sude.GeneratedTwinScan
