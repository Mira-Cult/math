import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15172)) 230162477 230195245 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 230162477 230195245).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15172 230162477 230195245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15173)) 230195245 230228013 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 230195245 230228013).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15173 230195245 230228013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15174)) 230228013 230260781 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 230228013 230260781).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15174 230228013 230260781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15175)) 230260781 230293549 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 230260781 230293549).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15175 230260781 230293549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 230162477 230228013).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 230162477 ≤ 230195245)
    (by decide : 230195245 ≤ 230228013) block0 block1

theorem join_0_1 : (twinPrimeSegment 230228013 230293549).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 230228013 ≤ 230260781)
    (by decide : 230260781 ≤ 230293549) block2 block3

theorem join_1_0 : (twinPrimeSegment 230162477 230293549).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 230162477 ≤ 230228013)
    (by decide : 230228013 ≤ 230293549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 230162477 230293549).card = 451 := join_1_0

end S109C12
end Sude.GeneratedTwinScan
