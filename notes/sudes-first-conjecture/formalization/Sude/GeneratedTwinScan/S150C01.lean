import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17740)) 314703917 314736685 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 314703917 314736685).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17740 314703917 314736685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17741)) 314736685 314769453 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 314736685 314769453).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17741 314736685 314769453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17742)) 314769453 314802221 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 314769453 314802221).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17742 314769453 314802221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17743)) 314802221 314834989 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 314802221 314834989).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17743 314802221 314834989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 314703917 314769453).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 314703917 ≤ 314736685)
    (by decide : 314736685 ≤ 314769453) block0 block1

theorem join_0_1 : (twinPrimeSegment 314769453 314834989).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 314769453 ≤ 314802221)
    (by decide : 314802221 ≤ 314834989) block2 block3

theorem join_1_0 : (twinPrimeSegment 314703917 314834989).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 314703917 ≤ 314769453)
    (by decide : 314769453 ≤ 314834989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 314703917 314834989).card = 444 := join_1_0

end S150C01
end Sude.GeneratedTwinScan
