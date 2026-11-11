import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18556)) 344326189 344358957 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 344326189 344358957).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18556 344326189 344358957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18557)) 344358957 344391725 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 344358957 344391725).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18557 344358957 344391725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18558)) 344391725 344424493 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 344391725 344424493).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18558 344391725 344424493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18559)) 344424493 344457261 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 344424493 344457261).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18559 344424493 344457261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 344326189 344391725).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 344326189 ≤ 344358957)
    (by decide : 344358957 ≤ 344391725) block0 block1

theorem join_0_1 : (twinPrimeSegment 344391725 344457261).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 344391725 ≤ 344424493)
    (by decide : 344424493 ≤ 344457261) block2 block3

theorem join_1_0 : (twinPrimeSegment 344326189 344457261).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 344326189 ≤ 344391725)
    (by decide : 344391725 ≤ 344457261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 344326189 344457261).card = 430 := join_1_0

end S164C03
end Sude.GeneratedTwinScan
