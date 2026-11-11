import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13999)) 195952685 195985453 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 195952685 195985453).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13999 195952685 195985453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14000)) 195985453 196018221 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 195985453 196018221).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14000 195985453 196018221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14001)) 196018221 196050989 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 196018221 196050989).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14001 196018221 196050989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14002)) 196050989 196083757 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 196050989 196083757).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14002 196050989 196083757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 195952685 196018221).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 195952685 ≤ 195985453)
    (by decide : 195985453 ≤ 196018221) block0 block1

theorem join_0_1 : (twinPrimeSegment 196018221 196083757).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 196018221 ≤ 196050989)
    (by decide : 196050989 ≤ 196083757) block2 block3

theorem join_1_0 : (twinPrimeSegment 195952685 196083757).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 195952685 ≤ 196018221)
    (by decide : 196018221 ≤ 196083757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 195952685 196083757).card = 474 := join_1_0

end S093C07
end Sude.GeneratedTwinScan
