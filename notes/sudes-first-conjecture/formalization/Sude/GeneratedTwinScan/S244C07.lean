import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22641)) 512622637 512655405 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 512622637 512655405).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22641 512622637 512655405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22642)) 512655405 512688173 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 512655405 512688173).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22642 512655405 512688173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22643)) 512688173 512720941 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 512688173 512720941).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22643 512688173 512720941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22644)) 512720941 512753709 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 512720941 512753709).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22644 512720941 512753709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 512622637 512688173).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 512622637 ≤ 512655405)
    (by decide : 512655405 ≤ 512688173) block0 block1

theorem join_0_1 : (twinPrimeSegment 512688173 512753709).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 512688173 ≤ 512720941)
    (by decide : 512720941 ≤ 512753709) block2 block3

theorem join_1_0 : (twinPrimeSegment 512622637 512753709).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 512622637 ≤ 512688173)
    (by decide : 512688173 ≤ 512753709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 512622637 512753709).card = 415 := join_1_0

end S244C07
end Sude.GeneratedTwinScan
