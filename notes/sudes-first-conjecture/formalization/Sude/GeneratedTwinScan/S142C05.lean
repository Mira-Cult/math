import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17276)) 298450989 298483757 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 298450989 298483757).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17276 298450989 298483757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17277)) 298483757 298516525 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 298483757 298516525).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17277 298483757 298516525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17278)) 298516525 298549293 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 298516525 298549293).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17278 298516525 298549293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17279)) 298549293 298582061 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 298549293 298582061).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17279 298549293 298582061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 298450989 298516525).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 298450989 ≤ 298483757)
    (by decide : 298483757 ≤ 298516525) block0 block1

theorem join_0_1 : (twinPrimeSegment 298516525 298582061).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 298516525 ≤ 298549293)
    (by decide : 298549293 ≤ 298582061) block2 block3

theorem join_1_0 : (twinPrimeSegment 298450989 298582061).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 298450989 ≤ 298516525)
    (by decide : 298516525 ≤ 298582061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 298450989 298582061).card = 461 := join_1_0

end S142C05
end Sude.GeneratedTwinScan
