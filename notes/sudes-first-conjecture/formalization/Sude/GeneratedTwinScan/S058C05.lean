import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122290221 122322989 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 122290221 122322989).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122290221 122322989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122322989 122355757 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 122322989 122355757).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122322989 122355757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122355757 122388525 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 122355757 122388525).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122355757 122388525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122388525 122421293 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 122388525 122421293).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122388525 122421293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 122290221 122355757).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 122290221 ≤ 122322989)
    (by decide : 122322989 ≤ 122355757) block0 block1

theorem join_0_1 : (twinPrimeSegment 122355757 122421293).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 122355757 ≤ 122388525)
    (by decide : 122388525 ≤ 122421293) block2 block3

theorem join_1_0 : (twinPrimeSegment 122290221 122421293).card = 505 := by
  simpa using combineTwinPrimeSegments (by decide : 122290221 ≤ 122355757)
    (by decide : 122355757 ≤ 122421293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 122290221 122421293).card = 505 := join_1_0

end S058C05
end Sude.GeneratedTwinScan
