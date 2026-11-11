import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15361)) 235929645 235962413 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 235929645 235962413).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15361 235929645 235962413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15362)) 235962413 235995181 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 235962413 235995181).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15362 235962413 235995181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15363)) 235995181 236027949 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 235995181 236027949).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15363 235995181 236027949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15364)) 236027949 236060717 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 236027949 236060717).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15364 236027949 236060717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 235929645 235995181).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 235929645 ≤ 235962413)
    (by decide : 235962413 ≤ 235995181) block0 block1

theorem join_0_1 : (twinPrimeSegment 235995181 236060717).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 235995181 ≤ 236027949)
    (by decide : 236027949 ≤ 236060717) block2 block3

theorem join_1_0 : (twinPrimeSegment 235929645 236060717).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 235929645 ≤ 235995181)
    (by decide : 235995181 ≤ 236060717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 235929645 236060717).card = 480 := join_1_0

end S112C08
end Sude.GeneratedTwinScan
