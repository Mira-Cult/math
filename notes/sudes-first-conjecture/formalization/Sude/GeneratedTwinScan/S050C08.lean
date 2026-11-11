import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105906221 105938989 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 105906221 105938989).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105906221 105938989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105938989 105971757 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 105938989 105971757).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105938989 105971757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105971757 106004525 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 105971757 106004525).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105971757 106004525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106004525 106037293 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 106004525 106037293).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106004525 106037293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 105906221 105971757).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 105906221 ≤ 105938989)
    (by decide : 105938989 ≤ 105971757) block0 block1

theorem join_0_1 : (twinPrimeSegment 105971757 106037293).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 105971757 ≤ 106004525)
    (by decide : 106004525 ≤ 106037293) block2 block3

theorem join_1_0 : (twinPrimeSegment 105906221 106037293).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 105906221 ≤ 105971757)
    (by decide : 105971757 ≤ 106037293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 105906221 106037293).card = 512 := join_1_0

end S050C08
end Sude.GeneratedTwinScan
