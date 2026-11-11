import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15568)) 242352173 242384941 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 242352173 242384941).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15568 242352173 242384941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15569)) 242384941 242417709 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 242384941 242417709).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15569 242384941 242417709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15570)) 242417709 242450477 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 242417709 242450477).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15570 242417709 242450477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15571)) 242450477 242483245 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 242450477 242483245).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15571 242450477 242483245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 242352173 242417709).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 242352173 ≤ 242384941)
    (by decide : 242384941 ≤ 242417709) block0 block1

theorem join_0_1 : (twinPrimeSegment 242417709 242483245).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 242417709 ≤ 242450477)
    (by decide : 242450477 ≤ 242483245) block2 block3

theorem join_1_0 : (twinPrimeSegment 242352173 242483245).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 242352173 ≤ 242417709)
    (by decide : 242417709 ≤ 242483245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 242352173 242483245).card = 454 := join_1_0

end S115C09
end Sude.GeneratedTwinScan
