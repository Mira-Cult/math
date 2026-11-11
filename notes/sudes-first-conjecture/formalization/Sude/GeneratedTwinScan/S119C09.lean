import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15835)) 250740781 250773549 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 250740781 250773549).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15835 250740781 250773549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15836)) 250773549 250806317 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 250773549 250806317).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15836 250773549 250806317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15837)) 250806317 250839085 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 250806317 250839085).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15837 250806317 250839085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15838)) 250839085 250871853 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 250839085 250871853).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15838 250839085 250871853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 250740781 250806317).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 250740781 ≤ 250773549)
    (by decide : 250773549 ≤ 250806317) block0 block1

theorem join_0_1 : (twinPrimeSegment 250806317 250871853).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 250806317 ≤ 250839085)
    (by decide : 250839085 ≤ 250871853) block2 block3

theorem join_1_0 : (twinPrimeSegment 250740781 250871853).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 250740781 ≤ 250806317)
    (by decide : 250806317 ≤ 250871853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 250740781 250871853).card = 468 := join_1_0

end S119C09
end Sude.GeneratedTwinScan
