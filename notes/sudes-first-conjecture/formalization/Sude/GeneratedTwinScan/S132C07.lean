import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16666)) 277741613 277774381 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 277741613 277774381).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16666 277741613 277774381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16667)) 277774381 277807149 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 277774381 277807149).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16667 277774381 277807149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16668)) 277807149 277839917 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 277807149 277839917).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16668 277807149 277839917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16669)) 277839917 277872685 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 277839917 277872685).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16669 277839917 277872685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 277741613 277807149).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 277741613 ≤ 277774381)
    (by decide : 277774381 ≤ 277807149) block0 block1

theorem join_0_1 : (twinPrimeSegment 277807149 277872685).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 277807149 ≤ 277839917)
    (by decide : 277839917 ≤ 277872685) block2 block3

theorem join_1_0 : (twinPrimeSegment 277741613 277872685).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 277741613 ≤ 277807149)
    (by decide : 277807149 ≤ 277872685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 277741613 277872685).card = 499 := join_1_0

end S132C07
end Sude.GeneratedTwinScan
