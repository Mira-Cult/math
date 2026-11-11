import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19995)) 399769645 399802413 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 399769645 399802413).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19995 399769645 399802413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19995)) 399802413 399835181 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 399802413 399835181).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19995 399802413 399835181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19996)) 399835181 399867949 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 399835181 399867949).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19996 399835181 399867949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19997)) 399867949 399900717 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 399867949 399900717).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19997 399867949 399900717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 399769645 399835181).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 399769645 ≤ 399802413)
    (by decide : 399802413 ≤ 399835181) block0 block1

theorem join_0_1 : (twinPrimeSegment 399835181 399900717).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 399835181 ≤ 399867949)
    (by decide : 399867949 ≤ 399900717) block2 block3

theorem join_1_0 : (twinPrimeSegment 399769645 399900717).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 399769645 ≤ 399835181)
    (by decide : 399835181 ≤ 399900717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 399769645 399900717).card = 437 := join_1_0

end S190C10
end Sude.GeneratedTwinScan
