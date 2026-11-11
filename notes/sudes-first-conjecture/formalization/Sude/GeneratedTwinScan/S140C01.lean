import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17139)) 293732397 293765165 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 293732397 293765165).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17139 293732397 293765165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17140)) 293765165 293797933 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 293765165 293797933).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17140 293765165 293797933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17141)) 293797933 293830701 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 293797933 293830701).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17141 293797933 293830701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17142)) 293830701 293863469 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 293830701 293863469).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17142 293830701 293863469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 293732397 293797933).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 293732397 ≤ 293765165)
    (by decide : 293765165 ≤ 293797933) block0 block1

theorem join_0_1 : (twinPrimeSegment 293797933 293863469).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 293797933 ≤ 293830701)
    (by decide : 293830701 ≤ 293863469) block2 block3

theorem join_1_0 : (twinPrimeSegment 293732397 293863469).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 293732397 ≤ 293797933)
    (by decide : 293797933 ≤ 293863469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 293732397 293863469).card = 461 := join_1_0

end S140C01
end Sude.GeneratedTwinScan
