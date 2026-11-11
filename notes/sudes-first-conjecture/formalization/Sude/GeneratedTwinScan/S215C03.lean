import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21244)) 451280941 451313709 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 451280941 451313709).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21244 451280941 451313709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21244)) 451313709 451346477 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 451313709 451346477).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21244 451313709 451346477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21245)) 451346477 451379245 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 451346477 451379245).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21245 451346477 451379245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21246)) 451379245 451412013 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 451379245 451412013).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21246 451379245 451412013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 451280941 451346477).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 451280941 ≤ 451313709)
    (by decide : 451313709 ≤ 451346477) block0 block1

theorem join_0_1 : (twinPrimeSegment 451346477 451412013).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 451346477 ≤ 451379245)
    (by decide : 451379245 ≤ 451412013) block2 block3

theorem join_1_0 : (twinPrimeSegment 451280941 451412013).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 451280941 ≤ 451346477)
    (by decide : 451346477 ≤ 451412013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 451280941 451412013).card = 444 := join_1_0

end S215C03
end Sude.GeneratedTwinScan
