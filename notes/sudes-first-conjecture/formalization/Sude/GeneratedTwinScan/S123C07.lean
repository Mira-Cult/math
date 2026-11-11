import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16090)) 258867245 258900013 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 258867245 258900013).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16090 258867245 258900013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16091)) 258900013 258932781 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 258900013 258932781).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16091 258900013 258932781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16092)) 258932781 258965549 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 258932781 258965549).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16092 258932781 258965549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16093)) 258965549 258998317 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 258965549 258998317).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16093 258965549 258998317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 258867245 258932781).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 258867245 ≤ 258900013)
    (by decide : 258900013 ≤ 258932781) block0 block1

theorem join_0_1 : (twinPrimeSegment 258932781 258998317).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 258932781 ≤ 258965549)
    (by decide : 258965549 ≤ 258998317) block2 block3

theorem join_1_0 : (twinPrimeSegment 258867245 258998317).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 258867245 ≤ 258932781)
    (by decide : 258932781 ≤ 258998317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 258867245 258998317).card = 461 := join_1_0

end S123C07
end Sude.GeneratedTwinScan
