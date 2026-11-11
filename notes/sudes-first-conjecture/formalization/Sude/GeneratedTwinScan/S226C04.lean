import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21783)) 474480685 474513453 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 474480685 474513453).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21783 474480685 474513453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21784)) 474513453 474546221 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 474513453 474546221).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21784 474513453 474546221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21784)) 474546221 474578989 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 474546221 474578989).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21784 474546221 474578989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21785)) 474578989 474611757 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 474578989 474611757).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21785 474578989 474611757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 474480685 474546221).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 474480685 ≤ 474513453)
    (by decide : 474513453 ≤ 474546221) block0 block1

theorem join_0_1 : (twinPrimeSegment 474546221 474611757).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 474546221 ≤ 474578989)
    (by decide : 474578989 ≤ 474611757) block2 block3

theorem join_1_0 : (twinPrimeSegment 474480685 474611757).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 474480685 ≤ 474546221)
    (by decide : 474546221 ≤ 474611757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 474480685 474611757).card = 443 := join_1_0

end S226C04
end Sude.GeneratedTwinScan
