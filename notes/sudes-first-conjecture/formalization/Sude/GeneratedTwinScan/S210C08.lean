import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S210C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21011)) 441450541 441483309 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 441450541 441483309).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21011 441450541 441483309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21012)) 441483309 441516077 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 441483309 441516077).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21012 441483309 441516077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21013)) 441516077 441548845 = 91 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 441516077 441548845).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21013 441516077 441548845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21013)) 441548845 441581613 = 86 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 441548845 441581613).card = 86 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21013 441548845 441581613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 441450541 441516077).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 441450541 ≤ 441483309)
    (by decide : 441483309 ≤ 441516077) block0 block1

theorem join_0_1 : (twinPrimeSegment 441516077 441581613).card = 177 := by
  simpa using combineTwinPrimeSegments (by decide : 441516077 ≤ 441548845)
    (by decide : 441548845 ≤ 441581613) block2 block3

theorem join_1_0 : (twinPrimeSegment 441450541 441581613).card = 387 := by
  simpa using combineTwinPrimeSegments (by decide : 441450541 ≤ 441516077)
    (by decide : 441516077 ≤ 441581613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 441450541 441581613).card = 387 := join_1_0

end S210C08
end Sude.GeneratedTwinScan
