import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20458)) 418512941 418545709 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 418512941 418545709).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20458 418512941 418545709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20459)) 418545709 418578477 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 418545709 418578477).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20459 418545709 418578477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20459)) 418578477 418611245 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 418578477 418611245).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20459 418578477 418611245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20460)) 418611245 418644013 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 418611245 418644013).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20460 418611245 418644013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 418512941 418578477).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 418512941 ≤ 418545709)
    (by decide : 418545709 ≤ 418578477) block0 block1

theorem join_0_1 : (twinPrimeSegment 418578477 418644013).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 418578477 ≤ 418611245)
    (by decide : 418611245 ≤ 418644013) block2 block3

theorem join_1_0 : (twinPrimeSegment 418512941 418644013).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 418512941 ≤ 418578477)
    (by decide : 418578477 ≤ 418644013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 418512941 418644013).card = 441 := join_1_0

end S199C09
end Sude.GeneratedTwinScan
