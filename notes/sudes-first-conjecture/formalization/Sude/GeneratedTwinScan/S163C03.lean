import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18500)) 342229037 342261805 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 342229037 342261805).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18500 342229037 342261805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18501)) 342261805 342294573 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 342261805 342294573).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18501 342261805 342294573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18502)) 342294573 342327341 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 342294573 342327341).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18502 342294573 342327341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18502)) 342327341 342360109 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 342327341 342360109).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18502 342327341 342360109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 342229037 342294573).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 342229037 ≤ 342261805)
    (by decide : 342261805 ≤ 342294573) block0 block1

theorem join_0_1 : (twinPrimeSegment 342294573 342360109).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 342294573 ≤ 342327341)
    (by decide : 342327341 ≤ 342360109) block2 block3

theorem join_1_0 : (twinPrimeSegment 342229037 342360109).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 342229037 ≤ 342294573)
    (by decide : 342294573 ≤ 342360109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 342229037 342360109).card = 465 := join_1_0

end S163C03
end Sude.GeneratedTwinScan
