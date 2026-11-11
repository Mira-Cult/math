import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22783)) 519045165 519077933 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 519045165 519077933).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22783 519045165 519077933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22784)) 519077933 519110701 = 93 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 519077933 519110701).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22784 519077933 519110701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22784)) 519110701 519143469 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 519110701 519143469).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22784 519110701 519143469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22785)) 519143469 519176237 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 519143469 519176237).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22785 519143469 519176237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 519045165 519110701).card = 186 := by
  simpa using combineTwinPrimeSegments (by decide : 519045165 ≤ 519077933)
    (by decide : 519077933 ≤ 519110701) block0 block1

theorem join_0_1 : (twinPrimeSegment 519110701 519176237).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 519110701 ≤ 519143469)
    (by decide : 519143469 ≤ 519176237) block2 block3

theorem join_1_0 : (twinPrimeSegment 519045165 519176237).card = 390 := by
  simpa using combineTwinPrimeSegments (by decide : 519045165 ≤ 519110701)
    (by decide : 519110701 ≤ 519176237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 519045165 519176237).card = 390 := join_1_0

end S247C08
end Sude.GeneratedTwinScan
