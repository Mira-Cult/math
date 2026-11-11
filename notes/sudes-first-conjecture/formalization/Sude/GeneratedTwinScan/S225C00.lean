import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21723)) 471859245 471892013 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 471859245 471892013).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21723 471859245 471892013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21723)) 471892013 471924781 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 471892013 471924781).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21723 471892013 471924781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21724)) 471924781 471957549 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 471924781 471957549).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21724 471924781 471957549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21725)) 471957549 471990317 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 471957549 471990317).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21725 471957549 471990317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 471859245 471924781).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 471859245 ≤ 471892013)
    (by decide : 471892013 ≤ 471924781) block0 block1

theorem join_0_1 : (twinPrimeSegment 471924781 471990317).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 471924781 ≤ 471957549)
    (by decide : 471957549 ≤ 471990317) block2 block3

theorem join_1_0 : (twinPrimeSegment 471859245 471990317).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 471859245 ≤ 471924781)
    (by decide : 471924781 ≤ 471990317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 471859245 471990317).card = 426 := join_1_0

end S225C00
end Sude.GeneratedTwinScan
