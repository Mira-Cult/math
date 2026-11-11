import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20936)) 438304813 438337581 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 438304813 438337581).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20936 438304813 438337581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20937)) 438337581 438370349 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 438337581 438370349).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20937 438337581 438370349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20938)) 438370349 438403117 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 438370349 438403117).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20938 438370349 438403117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20938)) 438403117 438435885 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 438403117 438435885).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20938 438403117 438435885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 438304813 438370349).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 438304813 ≤ 438337581)
    (by decide : 438337581 ≤ 438370349) block0 block1

theorem join_0_1 : (twinPrimeSegment 438370349 438435885).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 438370349 ≤ 438403117)
    (by decide : 438403117 ≤ 438435885) block2 block3

theorem join_1_0 : (twinPrimeSegment 438304813 438435885).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 438304813 ≤ 438370349)
    (by decide : 438370349 ≤ 438435885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 438304813 438435885).card = 466 := join_1_0

end S209C00
end Sude.GeneratedTwinScan
