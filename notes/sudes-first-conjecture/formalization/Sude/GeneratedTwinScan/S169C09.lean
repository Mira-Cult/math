import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18858)) 355598381 355631149 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 355598381 355631149).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18858 355598381 355631149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18859)) 355631149 355663917 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 355631149 355663917).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18859 355631149 355663917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18859)) 355663917 355696685 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 355663917 355696685).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18859 355663917 355696685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18860)) 355696685 355729453 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 355696685 355729453).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18860 355696685 355729453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 355598381 355663917).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 355598381 ≤ 355631149)
    (by decide : 355631149 ≤ 355663917) block0 block1

theorem join_0_1 : (twinPrimeSegment 355663917 355729453).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 355663917 ≤ 355696685)
    (by decide : 355696685 ≤ 355729453) block2 block3

theorem join_1_0 : (twinPrimeSegment 355598381 355729453).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 355598381 ≤ 355663917)
    (by decide : 355663917 ≤ 355729453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 355598381 355729453).card = 440 := join_1_0

end S169C09
end Sude.GeneratedTwinScan
