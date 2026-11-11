import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22560)) 508952621 508985389 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 508952621 508985389).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22560 508952621 508985389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22561)) 508985389 509018157 = 88 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 508985389 509018157).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22561 508985389 509018157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22562)) 509018157 509050925 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 509018157 509050925).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22562 509018157 509050925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22562)) 509050925 509083693 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 509050925 509083693).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22562 509050925 509083693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 508952621 509018157).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 508952621 ≤ 508985389)
    (by decide : 508985389 ≤ 509018157) block0 block1

theorem join_0_1 : (twinPrimeSegment 509018157 509083693).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 509018157 ≤ 509050925)
    (by decide : 509050925 ≤ 509083693) block2 block3

theorem join_1_0 : (twinPrimeSegment 508952621 509083693).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 508952621 ≤ 509018157)
    (by decide : 509018157 ≤ 509083693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 508952621 509083693).card = 439 := join_1_0

end S242C11
end Sude.GeneratedTwinScan
