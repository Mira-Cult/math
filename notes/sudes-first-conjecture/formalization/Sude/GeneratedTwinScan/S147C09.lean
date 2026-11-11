import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17592)) 309461037 309493805 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 309461037 309493805).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17592 309461037 309493805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17593)) 309493805 309526573 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 309493805 309526573).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17593 309493805 309526573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17594)) 309526573 309559341 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 309526573 309559341).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17594 309526573 309559341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17595)) 309559341 309592109 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 309559341 309592109).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17595 309559341 309592109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 309461037 309526573).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 309461037 ≤ 309493805)
    (by decide : 309493805 ≤ 309526573) block0 block1

theorem join_0_1 : (twinPrimeSegment 309526573 309592109).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 309526573 ≤ 309559341)
    (by decide : 309559341 ≤ 309592109) block2 block3

theorem join_1_0 : (twinPrimeSegment 309461037 309592109).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 309461037 ≤ 309526573)
    (by decide : 309526573 ≤ 309592109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 309461037 309592109).card = 423 := join_1_0

end S147C09
end Sude.GeneratedTwinScan
