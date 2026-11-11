import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20967)) 439615533 439648301 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 439615533 439648301).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20967 439615533 439648301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20968)) 439648301 439681069 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 439648301 439681069).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20968 439648301 439681069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20969)) 439681069 439713837 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 439681069 439713837).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20969 439681069 439713837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20970)) 439713837 439746605 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 439713837 439746605).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20970 439713837 439746605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 439615533 439681069).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 439615533 ≤ 439648301)
    (by decide : 439648301 ≤ 439681069) block0 block1

theorem join_0_1 : (twinPrimeSegment 439681069 439746605).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 439681069 ≤ 439713837)
    (by decide : 439713837 ≤ 439746605) block2 block3

theorem join_1_0 : (twinPrimeSegment 439615533 439746605).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 439615533 ≤ 439681069)
    (by decide : 439681069 ≤ 439746605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 439615533 439746605).card = 417 := join_1_0

end S209C10
end Sude.GeneratedTwinScan
