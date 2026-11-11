import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14148)) 200146989 200179757 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 200146989 200179757).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14148 200146989 200179757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14149)) 200179757 200212525 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 200179757 200212525).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14149 200179757 200212525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14150)) 200212525 200245293 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 200212525 200245293).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14150 200212525 200245293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14151)) 200245293 200278061 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 200245293 200278061).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14151 200245293 200278061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 200146989 200212525).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 200146989 ≤ 200179757)
    (by decide : 200179757 ≤ 200212525) block0 block1

theorem join_0_1 : (twinPrimeSegment 200212525 200278061).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 200212525 ≤ 200245293)
    (by decide : 200245293 ≤ 200278061) block2 block3

theorem join_1_0 : (twinPrimeSegment 200146989 200278061).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 200146989 ≤ 200212525)
    (by decide : 200212525 ≤ 200278061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 200146989 200278061).card = 485 := join_1_0

end S095C07
end Sude.GeneratedTwinScan
