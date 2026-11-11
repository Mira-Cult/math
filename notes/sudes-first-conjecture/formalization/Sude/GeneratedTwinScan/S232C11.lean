import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22091)) 487981101 488013869 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 487981101 488013869).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22091 487981101 488013869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22091)) 488013869 488046637 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 488013869 488046637).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22091 488013869 488046637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22092)) 488046637 488079405 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 488046637 488079405).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22092 488046637 488079405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22093)) 488079405 488112173 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 488079405 488112173).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22093 488079405 488112173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 487981101 488046637).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 487981101 ≤ 488013869)
    (by decide : 488013869 ≤ 488046637) block0 block1

theorem join_0_1 : (twinPrimeSegment 488046637 488112173).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 488046637 ≤ 488079405)
    (by decide : 488079405 ≤ 488112173) block2 block3

theorem join_1_0 : (twinPrimeSegment 487981101 488112173).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 487981101 ≤ 488046637)
    (by decide : 488046637 ≤ 488112173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 487981101 488112173).card = 420 := join_1_0

end S232C11
end Sude.GeneratedTwinScan
