import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19741)) 389677101 389709869 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 389677101 389709869).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19741 389677101 389709869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19741)) 389709869 389742637 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 389709869 389742637).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19741 389709869 389742637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19742)) 389742637 389775405 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 389742637 389775405).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19742 389742637 389775405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19743)) 389775405 389808173 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 389775405 389808173).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19743 389775405 389808173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 389677101 389742637).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 389677101 ≤ 389709869)
    (by decide : 389709869 ≤ 389742637) block0 block1

theorem join_0_1 : (twinPrimeSegment 389742637 389808173).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 389742637 ≤ 389775405)
    (by decide : 389775405 ≤ 389808173) block2 block3

theorem join_1_0 : (twinPrimeSegment 389677101 389808173).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 389677101 ≤ 389742637)
    (by decide : 389742637 ≤ 389808173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 389677101 389808173).card = 432 := join_1_0

end S185C13
end Sude.GeneratedTwinScan
