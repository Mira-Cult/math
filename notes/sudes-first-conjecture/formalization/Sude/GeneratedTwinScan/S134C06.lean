import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16788)) 281804845 281837613 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 281804845 281837613).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16788 281804845 281837613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16788)) 281837613 281870381 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 281837613 281870381).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16788 281837613 281870381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16789)) 281870381 281903149 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 281870381 281903149).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16789 281870381 281903149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16790)) 281903149 281935917 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 281903149 281935917).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16790 281903149 281935917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 281804845 281870381).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 281804845 ≤ 281837613)
    (by decide : 281837613 ≤ 281870381) block0 block1

theorem join_0_1 : (twinPrimeSegment 281870381 281935917).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 281870381 ≤ 281903149)
    (by decide : 281903149 ≤ 281935917) block2 block3

theorem join_1_0 : (twinPrimeSegment 281804845 281935917).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 281804845 ≤ 281870381)
    (by decide : 281870381 ≤ 281935917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 281804845 281935917).card = 477 := join_1_0

end S134C06
end Sude.GeneratedTwinScan
