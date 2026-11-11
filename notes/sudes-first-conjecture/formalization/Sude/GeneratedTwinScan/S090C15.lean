import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13810)) 190709805 190742573 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 190709805 190742573).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13810 190709805 190742573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13812)) 190742573 190775341 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 190742573 190775341).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13812 190742573 190775341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13813)) 190775341 190808109 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 190775341 190808109).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13813 190775341 190808109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13814)) 190808109 190840877 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 190808109 190840877).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13814 190808109 190840877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 190709805 190775341).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 190709805 ≤ 190742573)
    (by decide : 190742573 ≤ 190775341) block0 block1

theorem join_0_1 : (twinPrimeSegment 190775341 190840877).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 190775341 ≤ 190808109)
    (by decide : 190808109 ≤ 190840877) block2 block3

theorem join_1_0 : (twinPrimeSegment 190709805 190840877).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 190709805 ≤ 190775341)
    (by decide : 190775341 ≤ 190840877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 190709805 190840877).card = 472 := join_1_0

end S090C15
end Sude.GeneratedTwinScan
