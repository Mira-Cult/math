import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98697261 98730029 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 98697261 98730029).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98697261 98730029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98730029 98762797 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 98730029 98762797).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98730029 98762797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98762797 98795565 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 98762797 98795565).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98762797 98795565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98795565 98828333 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 98795565 98828333).card = 104 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98795565 98828333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 98697261 98762797).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 98697261 ≤ 98730029)
    (by decide : 98730029 ≤ 98762797) block0 block1

theorem join_0_1 : (twinPrimeSegment 98762797 98828333).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 98762797 ≤ 98795565)
    (by decide : 98795565 ≤ 98828333) block2 block3

theorem join_1_0 : (twinPrimeSegment 98697261 98828333).card = 515 := by
  simpa using combineTwinPrimeSegments (by decide : 98697261 ≤ 98762797)
    (by decide : 98762797 ≤ 98828333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 98697261 98828333).card = 515 := join_1_0

end S047C01
end Sude.GeneratedTwinScan
