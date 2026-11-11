import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13600)) 184942637 184975405 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 184942637 184975405).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13600 184942637 184975405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13601)) 184975405 185008173 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 184975405 185008173).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13601 184975405 185008173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13602)) 185008173 185040941 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 185008173 185040941).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13602 185008173 185040941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13604)) 185040941 185073709 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 185040941 185073709).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13604 185040941 185073709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 184942637 185008173).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 184942637 ≤ 184975405)
    (by decide : 184975405 ≤ 185008173) block0 block1

theorem join_0_1 : (twinPrimeSegment 185008173 185073709).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 185008173 ≤ 185040941)
    (by decide : 185040941 ≤ 185073709) block2 block3

theorem join_1_0 : (twinPrimeSegment 184942637 185073709).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 184942637 ≤ 185008173)
    (by decide : 185008173 ≤ 185073709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 184942637 185073709).card = 442 := join_1_0

end S088C03
end Sude.GeneratedTwinScan
