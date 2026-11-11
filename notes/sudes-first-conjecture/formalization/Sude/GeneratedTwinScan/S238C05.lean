import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22356)) 499777581 499810349 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 499777581 499810349).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22356 499777581 499810349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22357)) 499810349 499843117 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 499810349 499843117).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22357 499810349 499843117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22357)) 499843117 499875885 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 499843117 499875885).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22357 499843117 499875885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22358)) 499875885 499908653 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 499875885 499908653).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22358 499875885 499908653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 499777581 499843117).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 499777581 ≤ 499810349)
    (by decide : 499810349 ≤ 499843117) block0 block1

theorem join_0_1 : (twinPrimeSegment 499843117 499908653).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 499843117 ≤ 499875885)
    (by decide : 499875885 ≤ 499908653) block2 block3

theorem join_1_0 : (twinPrimeSegment 499777581 499908653).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 499777581 ≤ 499843117)
    (by decide : 499843117 ≤ 499908653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 499777581 499908653).card = 426 := join_1_0

end S238C05
end Sude.GeneratedTwinScan
