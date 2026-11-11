import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16183)) 261881901 261914669 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 261881901 261914669).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16183 261881901 261914669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16184)) 261914669 261947437 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 261914669 261947437).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16184 261914669 261947437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16185)) 261947437 261980205 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 261947437 261980205).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16185 261947437 261980205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16186)) 261980205 262012973 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 261980205 262012973).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16186 261980205 262012973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 261881901 261947437).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 261881901 ≤ 261914669)
    (by decide : 261914669 ≤ 261947437) block0 block1

theorem join_0_1 : (twinPrimeSegment 261947437 262012973).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 261947437 ≤ 261980205)
    (by decide : 261980205 ≤ 262012973) block2 block3

theorem join_1_0 : (twinPrimeSegment 261881901 262012973).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 261881901 ≤ 261947437)
    (by decide : 261947437 ≤ 262012973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 261881901 262012973).card = 469 := join_1_0

end S124C14
end Sude.GeneratedTwinScan
