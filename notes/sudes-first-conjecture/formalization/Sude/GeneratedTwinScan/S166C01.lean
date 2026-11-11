import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18662)) 348258349 348291117 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 348258349 348291117).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18662 348258349 348291117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18663)) 348291117 348323885 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 348291117 348323885).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18663 348291117 348323885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18664)) 348323885 348356653 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 348323885 348356653).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18664 348323885 348356653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18665)) 348356653 348389421 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 348356653 348389421).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18665 348356653 348389421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 348258349 348323885).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 348258349 ≤ 348291117)
    (by decide : 348291117 ≤ 348323885) block0 block1

theorem join_0_1 : (twinPrimeSegment 348323885 348389421).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 348323885 ≤ 348356653)
    (by decide : 348356653 ≤ 348389421) block2 block3

theorem join_1_0 : (twinPrimeSegment 348258349 348389421).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 348258349 ≤ 348323885)
    (by decide : 348323885 ≤ 348389421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 348258349 348389421).card = 462 := join_1_0

end S166C01
end Sude.GeneratedTwinScan
