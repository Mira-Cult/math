import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76021805 76054573 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 76021805 76054573).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76021805 76054573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76054573 76087341 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 76054573 76087341).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76054573 76087341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76087341 76120109 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 76087341 76120109).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76087341 76120109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76120109 76152877 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 76120109 76152877).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76120109 76152877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 76021805 76087341).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 76021805 ≤ 76054573)
    (by decide : 76054573 ≤ 76087341) block0 block1

theorem join_0_1 : (twinPrimeSegment 76087341 76152877).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 76087341 ≤ 76120109)
    (by decide : 76120109 ≤ 76152877) block2 block3

theorem join_1_0 : (twinPrimeSegment 76021805 76152877).card = 551 := by
  simpa using combineTwinPrimeSegments (by decide : 76021805 ≤ 76087341)
    (by decide : 76087341 ≤ 76152877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 76021805 76152877).card = 551 := join_1_0

end S036C04
end Sude.GeneratedTwinScan
