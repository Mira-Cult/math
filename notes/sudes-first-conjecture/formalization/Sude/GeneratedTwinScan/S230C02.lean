import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21969)) 482607149 482639917 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 482607149 482639917).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21969 482607149 482639917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21969)) 482639917 482672685 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 482639917 482672685).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21969 482639917 482672685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21970)) 482672685 482705453 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 482672685 482705453).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21970 482672685 482705453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21971)) 482705453 482738221 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 482705453 482738221).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21971 482705453 482738221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 482607149 482672685).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 482607149 ≤ 482639917)
    (by decide : 482639917 ≤ 482672685) block0 block1

theorem join_0_1 : (twinPrimeSegment 482672685 482738221).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 482672685 ≤ 482705453)
    (by decide : 482705453 ≤ 482738221) block2 block3

theorem join_1_0 : (twinPrimeSegment 482607149 482738221).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 482607149 ≤ 482672685)
    (by decide : 482672685 ≤ 482738221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 482607149 482738221).card = 413 := join_1_0

end S230C02
end Sude.GeneratedTwinScan
