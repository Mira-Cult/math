import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17078)) 291635245 291668013 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 291635245 291668013).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17078 291635245 291668013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17079)) 291668013 291700781 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 291668013 291700781).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17079 291668013 291700781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17080)) 291700781 291733549 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 291700781 291733549).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17080 291700781 291733549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17081)) 291733549 291766317 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 291733549 291766317).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17081 291733549 291766317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 291635245 291700781).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 291635245 ≤ 291668013)
    (by decide : 291668013 ≤ 291700781) block0 block1

theorem join_0_1 : (twinPrimeSegment 291700781 291766317).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 291700781 ≤ 291733549)
    (by decide : 291733549 ≤ 291766317) block2 block3

theorem join_1_0 : (twinPrimeSegment 291635245 291766317).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 291635245 ≤ 291700781)
    (by decide : 291700781 ≤ 291766317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 291635245 291766317).card = 443 := join_1_0

end S139C01
end Sude.GeneratedTwinScan
