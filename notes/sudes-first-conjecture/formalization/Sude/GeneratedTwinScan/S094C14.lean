import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14106)) 198967341 199000109 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 198967341 199000109).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14106 198967341 199000109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14107)) 199000109 199032877 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 199000109 199032877).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14107 199000109 199032877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14109)) 199032877 199065645 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 199032877 199065645).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14109 199032877 199065645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14110)) 199065645 199098413 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 199065645 199098413).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14110 199065645 199098413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 198967341 199032877).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 198967341 ≤ 199000109)
    (by decide : 199000109 ≤ 199032877) block0 block1

theorem join_0_1 : (twinPrimeSegment 199032877 199098413).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 199032877 ≤ 199065645)
    (by decide : 199065645 ≤ 199098413) block2 block3

theorem join_1_0 : (twinPrimeSegment 198967341 199098413).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 198967341 ≤ 199032877)
    (by decide : 199032877 ≤ 199098413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 198967341 199098413).card = 462 := join_1_0

end S094C14
end Sude.GeneratedTwinScan
