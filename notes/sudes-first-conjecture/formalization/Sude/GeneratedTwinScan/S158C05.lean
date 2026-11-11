import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18221)) 332005421 332038189 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 332005421 332038189).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18221 332005421 332038189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18222)) 332038189 332070957 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 332038189 332070957).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18222 332038189 332070957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18223)) 332070957 332103725 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 332070957 332103725).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18223 332070957 332103725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18224)) 332103725 332136493 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 332103725 332136493).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18224 332103725 332136493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 332005421 332070957).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 332005421 ≤ 332038189)
    (by decide : 332038189 ≤ 332070957) block0 block1

theorem join_0_1 : (twinPrimeSegment 332070957 332136493).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 332070957 ≤ 332103725)
    (by decide : 332103725 ≤ 332136493) block2 block3

theorem join_1_0 : (twinPrimeSegment 332005421 332136493).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 332005421 ≤ 332070957)
    (by decide : 332070957 ≤ 332136493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 332005421 332136493).card = 478 := join_1_0

end S158C05
end Sude.GeneratedTwinScan
