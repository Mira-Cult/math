import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127402029 127434797 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 127402029 127434797).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127402029 127434797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127434797 127467565 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 127434797 127467565).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127434797 127467565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127467565 127500333 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 127467565 127500333).card = 105 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127467565 127500333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127500333 127533101 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 127500333 127533101).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127500333 127533101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 127402029 127467565).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 127402029 ≤ 127434797)
    (by decide : 127434797 ≤ 127467565) block0 block1

theorem join_0_1 : (twinPrimeSegment 127467565 127533101).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 127467565 ≤ 127500333)
    (by decide : 127500333 ≤ 127533101) block2 block3

theorem join_1_0 : (twinPrimeSegment 127402029 127533101).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 127402029 ≤ 127467565)
    (by decide : 127467565 ≤ 127533101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 127402029 127533101).card = 504 := join_1_0

end S060C12
end Sude.GeneratedTwinScan
