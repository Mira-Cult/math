import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20216)) 408682541 408715309 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 408682541 408715309).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20216 408682541 408715309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20217)) 408715309 408748077 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 408715309 408748077).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20217 408715309 408748077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20218)) 408748077 408780845 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 408748077 408780845).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20218 408748077 408780845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20219)) 408780845 408813613 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 408780845 408813613).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20219 408780845 408813613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 408682541 408748077).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 408682541 ≤ 408715309)
    (by decide : 408715309 ≤ 408748077) block0 block1

theorem join_0_1 : (twinPrimeSegment 408748077 408813613).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 408748077 ≤ 408780845)
    (by decide : 408780845 ≤ 408813613) block2 block3

theorem join_1_0 : (twinPrimeSegment 408682541 408813613).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 408682541 ≤ 408748077)
    (by decide : 408748077 ≤ 408813613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 408682541 408813613).card = 444 := join_1_0

end S194C14
end Sude.GeneratedTwinScan
