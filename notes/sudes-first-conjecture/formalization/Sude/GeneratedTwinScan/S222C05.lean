import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21592)) 466223149 466255917 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 466223149 466255917).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21592 466223149 466255917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21593)) 466255917 466288685 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 466255917 466288685).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21593 466255917 466288685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21594)) 466288685 466321453 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 466288685 466321453).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21594 466288685 466321453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21595)) 466321453 466354221 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 466321453 466354221).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21595 466321453 466354221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 466223149 466288685).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 466223149 ≤ 466255917)
    (by decide : 466255917 ≤ 466288685) block0 block1

theorem join_0_1 : (twinPrimeSegment 466288685 466354221).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 466288685 ≤ 466321453)
    (by decide : 466321453 ≤ 466354221) block2 block3

theorem join_1_0 : (twinPrimeSegment 466223149 466354221).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 466223149 ≤ 466288685)
    (by decide : 466288685 ≤ 466354221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 466223149 466354221).card = 429 := join_1_0

end S222C05
end Sude.GeneratedTwinScan
