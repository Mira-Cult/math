import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13109)) 171835437 171868205 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 171835437 171868205).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13109 171835437 171868205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13111)) 171868205 171900973 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 171868205 171900973).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13111 171868205 171900973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13112)) 171900973 171933741 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 171900973 171933741).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13112 171900973 171933741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13113)) 171933741 171966509 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 171933741 171966509).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13113 171933741 171966509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 171835437 171900973).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 171835437 ≤ 171868205)
    (by decide : 171868205 ≤ 171900973) block0 block1

theorem join_0_1 : (twinPrimeSegment 171900973 171966509).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 171900973 ≤ 171933741)
    (by decide : 171933741 ≤ 171966509) block2 block3

theorem join_1_0 : (twinPrimeSegment 171835437 171966509).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 171835437 ≤ 171900973)
    (by decide : 171900973 ≤ 171966509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 171835437 171966509).card = 484 := join_1_0

end S081C15
end Sude.GeneratedTwinScan
