import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17651)) 311558189 311590957 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 311558189 311590957).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17651 311558189 311590957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17652)) 311590957 311623725 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 311590957 311623725).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17652 311590957 311623725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17653)) 311623725 311656493 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 311623725 311656493).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17653 311623725 311656493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17654)) 311656493 311689261 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 311656493 311689261).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17654 311656493 311689261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 311558189 311623725).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 311558189 ≤ 311590957)
    (by decide : 311590957 ≤ 311623725) block0 block1

theorem join_0_1 : (twinPrimeSegment 311623725 311689261).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 311623725 ≤ 311656493)
    (by decide : 311656493 ≤ 311689261) block2 block3

theorem join_1_0 : (twinPrimeSegment 311558189 311689261).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 311558189 ≤ 311623725)
    (by decide : 311623725 ≤ 311689261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 311558189 311689261).card = 471 := join_1_0

end S148C09
end Sude.GeneratedTwinScan
