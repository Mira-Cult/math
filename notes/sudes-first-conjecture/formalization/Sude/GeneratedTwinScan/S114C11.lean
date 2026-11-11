import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15509)) 240517165 240549933 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 240517165 240549933).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15509 240517165 240549933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15510)) 240549933 240582701 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 240549933 240582701).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15510 240549933 240582701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15511)) 240582701 240615469 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 240582701 240615469).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15511 240582701 240615469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15512)) 240615469 240648237 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 240615469 240648237).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15512 240615469 240648237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 240517165 240582701).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 240517165 ≤ 240549933)
    (by decide : 240549933 ≤ 240582701) block0 block1

theorem join_0_1 : (twinPrimeSegment 240582701 240648237).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 240582701 ≤ 240615469)
    (by decide : 240615469 ≤ 240648237) block2 block3

theorem join_1_0 : (twinPrimeSegment 240517165 240648237).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 240517165 ≤ 240582701)
    (by decide : 240582701 ≤ 240648237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 240517165 240648237).card = 454 := join_1_0

end S114C11
end Sude.GeneratedTwinScan
