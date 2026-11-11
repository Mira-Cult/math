import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22473)) 505020461 505053229 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 505020461 505053229).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22473 505020461 505053229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22474)) 505053229 505085997 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 505053229 505085997).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22474 505053229 505085997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22474)) 505085997 505118765 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 505085997 505118765).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22474 505085997 505118765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22475)) 505118765 505151533 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 505118765 505151533).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22475 505118765 505151533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 505020461 505085997).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 505020461 ≤ 505053229)
    (by decide : 505053229 ≤ 505085997) block0 block1

theorem join_0_1 : (twinPrimeSegment 505085997 505151533).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 505085997 ≤ 505118765)
    (by decide : 505118765 ≤ 505151533) block2 block3

theorem join_1_0 : (twinPrimeSegment 505020461 505151533).card = 401 := by
  simpa using combineTwinPrimeSegments (by decide : 505020461 ≤ 505085997)
    (by decide : 505085997 ≤ 505151533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 505020461 505151533).card = 401 := join_1_0

end S240C13
end Sude.GeneratedTwinScan
