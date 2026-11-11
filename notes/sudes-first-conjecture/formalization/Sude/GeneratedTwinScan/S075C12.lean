import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12605)) 158859309 158892077 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 158859309 158892077).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12605 158859309 158892077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12606)) 158892077 158924845 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 158892077 158924845).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12606 158892077 158924845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12607)) 158924845 158957613 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 158924845 158957613).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12607 158924845 158957613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12609)) 158957613 158990381 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 158957613 158990381).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12609 158957613 158990381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 158859309 158924845).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 158859309 ≤ 158892077)
    (by decide : 158892077 ≤ 158924845) block0 block1

theorem join_0_1 : (twinPrimeSegment 158924845 158990381).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 158924845 ≤ 158957613)
    (by decide : 158957613 ≤ 158990381) block2 block3

theorem join_1_0 : (twinPrimeSegment 158859309 158990381).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 158859309 ≤ 158924845)
    (by decide : 158924845 ≤ 158990381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 158859309 158990381).card = 511 := join_1_0

end S075C12
end Sude.GeneratedTwinScan
