import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18447)) 340262957 340295725 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 340262957 340295725).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18447 340262957 340295725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18447)) 340295725 340328493 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 340295725 340328493).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18447 340295725 340328493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18448)) 340328493 340361261 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 340328493 340361261).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18448 340328493 340361261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18449)) 340361261 340394029 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 340361261 340394029).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18449 340361261 340394029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 340262957 340328493).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 340262957 ≤ 340295725)
    (by decide : 340295725 ≤ 340328493) block0 block1

theorem join_0_1 : (twinPrimeSegment 340328493 340394029).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 340328493 ≤ 340361261)
    (by decide : 340361261 ≤ 340394029) block2 block3

theorem join_1_0 : (twinPrimeSegment 340262957 340394029).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 340262957 ≤ 340328493)
    (by decide : 340328493 ≤ 340394029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 340262957 340394029).card = 463 := join_1_0

end S162C04
end Sude.GeneratedTwinScan
