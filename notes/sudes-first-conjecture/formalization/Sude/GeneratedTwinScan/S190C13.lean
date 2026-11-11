import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20004)) 400162861 400195629 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 400162861 400195629).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20004 400162861 400195629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20005)) 400195629 400228397 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 400195629 400228397).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20005 400195629 400228397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20006)) 400228397 400261165 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 400228397 400261165).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20006 400228397 400261165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20007)) 400261165 400293933 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 400261165 400293933).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20007 400261165 400293933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 400162861 400228397).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 400162861 ≤ 400195629)
    (by decide : 400195629 ≤ 400228397) block0 block1

theorem join_0_1 : (twinPrimeSegment 400228397 400293933).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 400228397 ≤ 400261165)
    (by decide : 400261165 ≤ 400293933) block2 block3

theorem join_1_0 : (twinPrimeSegment 400162861 400293933).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 400162861 ≤ 400228397)
    (by decide : 400228397 ≤ 400293933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 400162861 400293933).card = 425 := join_1_0

end S190C13
end Sude.GeneratedTwinScan
