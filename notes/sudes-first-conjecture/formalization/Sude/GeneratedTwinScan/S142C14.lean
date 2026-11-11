import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17310)) 299630637 299663405 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 299630637 299663405).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17310 299630637 299663405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17311)) 299663405 299696173 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 299663405 299696173).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17311 299663405 299696173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17312)) 299696173 299728941 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 299696173 299728941).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17312 299696173 299728941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17313)) 299728941 299761709 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 299728941 299761709).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17313 299728941 299761709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 299630637 299696173).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 299630637 ≤ 299663405)
    (by decide : 299663405 ≤ 299696173) block0 block1

theorem join_0_1 : (twinPrimeSegment 299696173 299761709).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 299696173 ≤ 299728941)
    (by decide : 299728941 ≤ 299761709) block2 block3

theorem join_1_0 : (twinPrimeSegment 299630637 299761709).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 299630637 ≤ 299696173)
    (by decide : 299696173 ≤ 299761709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 299630637 299761709).card = 420 := join_1_0

end S142C14
end Sude.GeneratedTwinScan
