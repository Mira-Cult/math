import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115081261 115114029 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 115081261 115114029).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115081261 115114029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115114029 115146797 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 115114029 115146797).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115114029 115146797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115146797 115179565 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 115146797 115179565).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115146797 115179565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115179565 115212333 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 115179565 115212333).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115179565 115212333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 115081261 115146797).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 115081261 ≤ 115114029)
    (by decide : 115114029 ≤ 115146797) block0 block1

theorem join_0_1 : (twinPrimeSegment 115146797 115212333).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 115146797 ≤ 115179565)
    (by decide : 115179565 ≤ 115212333) block2 block3

theorem join_1_0 : (twinPrimeSegment 115081261 115212333).card = 518 := by
  simpa using combineTwinPrimeSegments (by decide : 115081261 ≤ 115146797)
    (by decide : 115146797 ≤ 115212333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 115081261 115212333).card = 518 := join_1_0

end S054C14
end Sude.GeneratedTwinScan
