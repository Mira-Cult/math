import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17408)) 303038509 303071277 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 303038509 303071277).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17408 303038509 303071277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17409)) 303071277 303104045 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 303071277 303104045).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17409 303071277 303104045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17410)) 303104045 303136813 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 303104045 303136813).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17410 303104045 303136813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17411)) 303136813 303169581 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 303136813 303169581).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17411 303136813 303169581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 303038509 303104045).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 303038509 ≤ 303071277)
    (by decide : 303071277 ≤ 303104045) block0 block1

theorem join_0_1 : (twinPrimeSegment 303104045 303169581).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 303104045 ≤ 303136813)
    (by decide : 303136813 ≤ 303169581) block2 block3

theorem join_1_0 : (twinPrimeSegment 303038509 303169581).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 303038509 ≤ 303104045)
    (by decide : 303104045 ≤ 303169581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 303038509 303169581).card = 462 := join_1_0

end S144C08
end Sude.GeneratedTwinScan
