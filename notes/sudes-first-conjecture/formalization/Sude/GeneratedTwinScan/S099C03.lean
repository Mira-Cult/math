import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14423)) 208011309 208044077 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 208011309 208044077).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14423 208011309 208044077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14424)) 208044077 208076845 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 208044077 208076845).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14424 208044077 208076845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14426)) 208076845 208109613 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 208076845 208109613).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14426 208076845 208109613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14427)) 208109613 208142381 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 208109613 208142381).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14427 208109613 208142381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 208011309 208076845).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 208011309 ≤ 208044077)
    (by decide : 208044077 ≤ 208076845) block0 block1

theorem join_0_1 : (twinPrimeSegment 208076845 208142381).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 208076845 ≤ 208109613)
    (by decide : 208109613 ≤ 208142381) block2 block3

theorem join_1_0 : (twinPrimeSegment 208011309 208142381).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 208011309 ≤ 208076845)
    (by decide : 208076845 ≤ 208142381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 208011309 208142381).card = 473 := join_1_0

end S099C03
end Sude.GeneratedTwinScan
