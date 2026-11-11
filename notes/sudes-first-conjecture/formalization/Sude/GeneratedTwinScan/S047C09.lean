import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99745837 99778605 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 99745837 99778605).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99745837 99778605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99778605 99811373 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 99778605 99811373).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99778605 99811373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99811373 99844141 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 99811373 99844141).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99811373 99844141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99844141 99876909 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 99844141 99876909).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99844141 99876909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 99745837 99811373).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 99745837 ≤ 99778605)
    (by decide : 99778605 ≤ 99811373) block0 block1

theorem join_0_1 : (twinPrimeSegment 99811373 99876909).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 99811373 ≤ 99844141)
    (by decide : 99844141 ≤ 99876909) block2 block3

theorem join_1_0 : (twinPrimeSegment 99745837 99876909).card = 518 := by
  simpa using combineTwinPrimeSegments (by decide : 99745837 ≤ 99811373)
    (by decide : 99811373 ≤ 99876909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 99745837 99876909).card = 518 := join_1_0

end S047C09
end Sude.GeneratedTwinScan
