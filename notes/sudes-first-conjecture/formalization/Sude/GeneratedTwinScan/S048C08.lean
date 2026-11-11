import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101711917 101744685 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 101711917 101744685).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101711917 101744685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101744685 101777453 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 101744685 101777453).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101744685 101777453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101777453 101810221 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 101777453 101810221).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101777453 101810221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101810221 101842989 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 101810221 101842989).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101810221 101842989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 101711917 101777453).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 101711917 ≤ 101744685)
    (by decide : 101744685 ≤ 101777453) block0 block1

theorem join_0_1 : (twinPrimeSegment 101777453 101842989).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 101777453 ≤ 101810221)
    (by decide : 101810221 ≤ 101842989) block2 block3

theorem join_1_0 : (twinPrimeSegment 101711917 101842989).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 101711917 ≤ 101777453)
    (by decide : 101777453 ≤ 101842989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 101711917 101842989).card = 497 := join_1_0

end S048C08
end Sude.GeneratedTwinScan
