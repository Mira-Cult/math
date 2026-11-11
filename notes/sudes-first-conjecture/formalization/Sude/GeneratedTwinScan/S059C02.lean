import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123994157 124026925 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 123994157 124026925).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123994157 124026925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124026925 124059693 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 124026925 124059693).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124026925 124059693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124059693 124092461 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 124059693 124092461).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124059693 124092461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124092461 124125229 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 124092461 124125229).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124092461 124125229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 123994157 124059693).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 123994157 ≤ 124026925)
    (by decide : 124026925 ≤ 124059693) block0 block1

theorem join_0_1 : (twinPrimeSegment 124059693 124125229).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 124059693 ≤ 124092461)
    (by decide : 124092461 ≤ 124125229) block2 block3

theorem join_1_0 : (twinPrimeSegment 123994157 124125229).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 123994157 ≤ 124059693)
    (by decide : 124059693 ≤ 124125229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 123994157 124125229).card = 482 := join_1_0

end S059C02
end Sude.GeneratedTwinScan
