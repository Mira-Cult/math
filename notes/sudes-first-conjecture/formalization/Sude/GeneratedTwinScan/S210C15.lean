import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S210C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21033)) 442368045 442400813 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 442368045 442400813).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21033 442368045 442400813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21034)) 442400813 442433581 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 442400813 442433581).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21034 442400813 442433581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21034)) 442433581 442466349 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 442433581 442466349).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21034 442433581 442466349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21035)) 442466349 442499117 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 442466349 442499117).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21035 442466349 442499117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 442368045 442433581).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 442368045 ≤ 442400813)
    (by decide : 442400813 ≤ 442433581) block0 block1

theorem join_0_1 : (twinPrimeSegment 442433581 442499117).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 442433581 ≤ 442466349)
    (by decide : 442466349 ≤ 442499117) block2 block3

theorem join_1_0 : (twinPrimeSegment 442368045 442499117).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 442368045 ≤ 442433581)
    (by decide : 442433581 ≤ 442499117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 442368045 442499117).card = 441 := join_1_0

end S210C15
end Sude.GeneratedTwinScan
