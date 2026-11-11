import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17393)) 302514221 302546989 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 302514221 302546989).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17393 302514221 302546989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17394)) 302546989 302579757 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 302546989 302579757).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17394 302546989 302579757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17395)) 302579757 302612525 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 302579757 302612525).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17395 302579757 302612525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17396)) 302612525 302645293 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 302612525 302645293).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17396 302612525 302645293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 302514221 302579757).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 302514221 ≤ 302546989)
    (by decide : 302546989 ≤ 302579757) block0 block1

theorem join_0_1 : (twinPrimeSegment 302579757 302645293).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 302579757 ≤ 302612525)
    (by decide : 302612525 ≤ 302645293) block2 block3

theorem join_1_0 : (twinPrimeSegment 302514221 302645293).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 302514221 ≤ 302579757)
    (by decide : 302579757 ≤ 302645293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 302514221 302645293).card = 475 := join_1_0

end S144C04
end Sude.GeneratedTwinScan
