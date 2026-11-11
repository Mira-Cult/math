import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22274)) 496107565 496140333 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 496107565 496140333).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22274 496107565 496140333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22274)) 496140333 496173101 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 496140333 496173101).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22274 496140333 496173101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22275)) 496173101 496205869 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 496173101 496205869).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22275 496173101 496205869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22276)) 496205869 496238637 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 496205869 496238637).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22276 496205869 496238637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 496107565 496173101).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 496107565 ≤ 496140333)
    (by decide : 496140333 ≤ 496173101) block0 block1

theorem join_0_1 : (twinPrimeSegment 496173101 496238637).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 496173101 ≤ 496205869)
    (by decide : 496205869 ≤ 496238637) block2 block3

theorem join_1_0 : (twinPrimeSegment 496107565 496238637).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 496107565 ≤ 496173101)
    (by decide : 496173101 ≤ 496238637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 496107565 496238637).card = 449 := join_1_0

end S236C09
end Sude.GeneratedTwinScan
