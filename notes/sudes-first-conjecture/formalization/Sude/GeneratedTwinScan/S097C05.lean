import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14286)) 204079149 204111917 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 204079149 204111917).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14286 204079149 204111917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14287)) 204111917 204144685 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 204111917 204144685).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14287 204111917 204144685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14289)) 204144685 204177453 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 204144685 204177453).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14289 204144685 204177453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14290)) 204177453 204210221 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 204177453 204210221).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14290 204177453 204210221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 204079149 204144685).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 204079149 ≤ 204111917)
    (by decide : 204111917 ≤ 204144685) block0 block1

theorem join_0_1 : (twinPrimeSegment 204144685 204210221).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 204144685 ≤ 204177453)
    (by decide : 204177453 ≤ 204210221) block2 block3

theorem join_1_0 : (twinPrimeSegment 204079149 204210221).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 204079149 ≤ 204144685)
    (by decide : 204144685 ≤ 204210221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 204079149 204210221).card = 456 := join_1_0

end S097C05
end Sude.GeneratedTwinScan
