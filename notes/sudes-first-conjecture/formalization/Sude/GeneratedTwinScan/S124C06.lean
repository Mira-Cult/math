import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16151)) 260833325 260866093 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 260833325 260866093).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16151 260833325 260866093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16152)) 260866093 260898861 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 260866093 260898861).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16152 260866093 260898861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16153)) 260898861 260931629 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 260898861 260931629).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16153 260898861 260931629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16154)) 260931629 260964397 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 260931629 260964397).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16154 260931629 260964397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 260833325 260898861).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 260833325 ≤ 260866093)
    (by decide : 260866093 ≤ 260898861) block0 block1

theorem join_0_1 : (twinPrimeSegment 260898861 260964397).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 260898861 ≤ 260931629)
    (by decide : 260931629 ≤ 260964397) block2 block3

theorem join_1_0 : (twinPrimeSegment 260833325 260964397).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 260833325 ≤ 260898861)
    (by decide : 260898861 ≤ 260964397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 260833325 260964397).card = 497 := join_1_0

end S124C06
end Sude.GeneratedTwinScan
