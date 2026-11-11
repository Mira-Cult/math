import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123863085 123895853 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 123863085 123895853).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123863085 123895853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123895853 123928621 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 123895853 123928621).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123895853 123928621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123928621 123961389 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 123928621 123961389).card = 106 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123928621 123961389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123961389 123994157 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 123961389 123994157).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123961389 123994157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 123863085 123928621).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 123863085 ≤ 123895853)
    (by decide : 123895853 ≤ 123928621) block0 block1

theorem join_0_1 : (twinPrimeSegment 123928621 123994157).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 123928621 ≤ 123961389)
    (by decide : 123961389 ≤ 123994157) block2 block3

theorem join_1_0 : (twinPrimeSegment 123863085 123994157).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 123863085 ≤ 123928621)
    (by decide : 123928621 ≤ 123994157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 123863085 123994157).card = 491 := join_1_0

end S059C01
end Sude.GeneratedTwinScan
