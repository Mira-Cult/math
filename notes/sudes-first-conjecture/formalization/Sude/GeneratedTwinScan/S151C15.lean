import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17851)) 318636077 318668845 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 318636077 318668845).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17851 318636077 318668845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17852)) 318668845 318701613 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 318668845 318701613).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17852 318668845 318701613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17853)) 318701613 318734381 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 318701613 318734381).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17853 318701613 318734381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17854)) 318734381 318767149 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 318734381 318767149).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17854 318734381 318767149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 318636077 318701613).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 318636077 ≤ 318668845)
    (by decide : 318668845 ≤ 318701613) block0 block1

theorem join_0_1 : (twinPrimeSegment 318701613 318767149).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 318701613 ≤ 318734381)
    (by decide : 318734381 ≤ 318767149) block2 block3

theorem join_1_0 : (twinPrimeSegment 318636077 318767149).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 318636077 ≤ 318701613)
    (by decide : 318701613 ≤ 318767149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 318636077 318767149).card = 477 := join_1_0

end S151C15
end Sude.GeneratedTwinScan
