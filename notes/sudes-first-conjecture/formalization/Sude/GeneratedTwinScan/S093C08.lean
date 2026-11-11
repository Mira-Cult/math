import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14004)) 196083757 196116525 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 196083757 196116525).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14004 196083757 196116525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14005)) 196116525 196149293 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 196116525 196149293).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14005 196116525 196149293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14006)) 196149293 196182061 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 196149293 196182061).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14006 196149293 196182061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14007)) 196182061 196214829 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 196182061 196214829).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14007 196182061 196214829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 196083757 196149293).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 196083757 ≤ 196116525)
    (by decide : 196116525 ≤ 196149293) block0 block1

theorem join_0_1 : (twinPrimeSegment 196149293 196214829).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 196149293 ≤ 196182061)
    (by decide : 196182061 ≤ 196214829) block2 block3

theorem join_1_0 : (twinPrimeSegment 196083757 196214829).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 196083757 ≤ 196149293)
    (by decide : 196149293 ≤ 196214829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 196083757 196214829).card = 466 := join_1_0

end S093C08
end Sude.GeneratedTwinScan
