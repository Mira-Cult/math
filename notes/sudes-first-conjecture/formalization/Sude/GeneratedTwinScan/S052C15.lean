import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111018029 111050797 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 111018029 111050797).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111018029 111050797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111050797 111083565 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 111050797 111083565).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111050797 111083565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111083565 111116333 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 111083565 111116333).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111083565 111116333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111116333 111149101 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 111116333 111149101).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111116333 111149101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 111018029 111083565).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 111018029 ≤ 111050797)
    (by decide : 111050797 ≤ 111083565) block0 block1

theorem join_0_1 : (twinPrimeSegment 111083565 111149101).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 111083565 ≤ 111116333)
    (by decide : 111116333 ≤ 111149101) block2 block3

theorem join_1_0 : (twinPrimeSegment 111018029 111149101).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 111018029 ≤ 111083565)
    (by decide : 111083565 ≤ 111149101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 111018029 111149101).card = 487 := join_1_0

end S052C15
end Sude.GeneratedTwinScan
