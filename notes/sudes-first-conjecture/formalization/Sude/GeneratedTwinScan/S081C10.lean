import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13084)) 171180077 171212845 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 171180077 171212845).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13084 171180077 171212845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13086)) 171212845 171245613 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 171212845 171245613).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13086 171212845 171245613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13087)) 171245613 171278381 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 171245613 171278381).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13087 171245613 171278381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13088)) 171278381 171311149 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 171278381 171311149).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13088 171278381 171311149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 171180077 171245613).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 171180077 ≤ 171212845)
    (by decide : 171212845 ≤ 171245613) block0 block1

theorem join_0_1 : (twinPrimeSegment 171245613 171311149).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 171245613 ≤ 171278381)
    (by decide : 171278381 ≤ 171311149) block2 block3

theorem join_1_0 : (twinPrimeSegment 171180077 171311149).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 171180077 ≤ 171245613)
    (by decide : 171245613 ≤ 171311149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 171180077 171311149).card = 451 := join_1_0

end S081C10
end Sude.GeneratedTwinScan
