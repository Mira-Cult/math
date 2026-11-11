import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17777)) 316014637 316047405 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 316014637 316047405).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17777 316014637 316047405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17778)) 316047405 316080173 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 316047405 316080173).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17778 316047405 316080173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17779)) 316080173 316112941 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 316080173 316112941).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17779 316080173 316112941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17780)) 316112941 316145709 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 316112941 316145709).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17780 316112941 316145709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 316014637 316080173).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 316014637 ≤ 316047405)
    (by decide : 316047405 ≤ 316080173) block0 block1

theorem join_0_1 : (twinPrimeSegment 316080173 316145709).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 316080173 ≤ 316112941)
    (by decide : 316112941 ≤ 316145709) block2 block3

theorem join_1_0 : (twinPrimeSegment 316014637 316145709).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 316014637 ≤ 316080173)
    (by decide : 316080173 ≤ 316145709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 316014637 316145709).card = 430 := join_1_0

end S150C11
end Sude.GeneratedTwinScan
