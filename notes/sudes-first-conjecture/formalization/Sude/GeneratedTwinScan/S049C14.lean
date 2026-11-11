import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104595501 104628269 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 104595501 104628269).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104595501 104628269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104628269 104661037 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 104628269 104661037).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104628269 104661037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104661037 104693805 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 104661037 104693805).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104661037 104693805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104693805 104726573 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 104693805 104726573).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104693805 104726573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 104595501 104661037).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 104595501 ≤ 104628269)
    (by decide : 104628269 ≤ 104661037) block0 block1

theorem join_0_1 : (twinPrimeSegment 104661037 104726573).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 104661037 ≤ 104693805)
    (by decide : 104693805 ≤ 104726573) block2 block3

theorem join_1_0 : (twinPrimeSegment 104595501 104726573).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 104595501 ≤ 104661037)
    (by decide : 104661037 ≤ 104726573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 104595501 104726573).card = 490 := join_1_0

end S049C14
end Sude.GeneratedTwinScan
