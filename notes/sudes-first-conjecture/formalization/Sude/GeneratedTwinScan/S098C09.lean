import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14378)) 206700589 206733357 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 206700589 206733357).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14378 206700589 206733357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14379)) 206733357 206766125 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 206733357 206766125).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14379 206733357 206766125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14380)) 206766125 206798893 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 206766125 206798893).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14380 206766125 206798893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14381)) 206798893 206831661 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 206798893 206831661).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14381 206798893 206831661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 206700589 206766125).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 206700589 ≤ 206733357)
    (by decide : 206733357 ≤ 206766125) block0 block1

theorem join_0_1 : (twinPrimeSegment 206766125 206831661).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 206766125 ≤ 206798893)
    (by decide : 206798893 ≤ 206831661) block2 block3

theorem join_1_0 : (twinPrimeSegment 206700589 206831661).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 206700589 ≤ 206766125)
    (by decide : 206766125 ≤ 206831661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 206700589 206831661).card = 491 := join_1_0

end S098C09
end Sude.GeneratedTwinScan
