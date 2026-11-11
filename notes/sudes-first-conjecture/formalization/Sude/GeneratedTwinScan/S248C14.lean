import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22846)) 521928749 521961517 = 88 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 521928749 521961517).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22846 521928749 521961517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22847)) 521961517 521994285 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 521961517 521994285).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22847 521961517 521994285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22847)) 521994285 522027053 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 521994285 522027053).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22847 521994285 522027053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22848)) 522027053 522059821 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 522027053 522059821).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22848 522027053 522059821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 521928749 521994285).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 521928749 ≤ 521961517)
    (by decide : 521961517 ≤ 521994285) block0 block1

theorem join_0_1 : (twinPrimeSegment 521994285 522059821).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 521994285 ≤ 522027053)
    (by decide : 522027053 ≤ 522059821) block2 block3

theorem join_1_0 : (twinPrimeSegment 521928749 522059821).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 521928749 ≤ 521994285)
    (by decide : 521994285 ≤ 522059821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 521928749 522059821).card = 430 := join_1_0

end S248C14
end Sude.GeneratedTwinScan
