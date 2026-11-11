import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19991)) 399638573 399671341 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 399638573 399671341).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19991 399638573 399671341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19992)) 399671341 399704109 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 399671341 399704109).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19992 399671341 399704109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19993)) 399704109 399736877 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 399704109 399736877).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19993 399704109 399736877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19994)) 399736877 399769645 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 399736877 399769645).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19994 399736877 399769645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 399638573 399704109).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 399638573 ≤ 399671341)
    (by decide : 399671341 ≤ 399704109) block0 block1

theorem join_0_1 : (twinPrimeSegment 399704109 399769645).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 399704109 ≤ 399736877)
    (by decide : 399736877 ≤ 399769645) block2 block3

theorem join_1_0 : (twinPrimeSegment 399638573 399769645).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 399638573 ≤ 399704109)
    (by decide : 399704109 ≤ 399769645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 399638573 399769645).card = 468 := join_1_0

end S190C09
end Sude.GeneratedTwinScan
