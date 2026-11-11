import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18896)) 357040173 357072941 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 357040173 357072941).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18896 357040173 357072941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18897)) 357072941 357105709 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 357072941 357105709).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18897 357072941 357105709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18898)) 357105709 357138477 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 357105709 357138477).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18898 357105709 357138477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18898)) 357138477 357171245 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 357138477 357171245).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18898 357138477 357171245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 357040173 357105709).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 357040173 ≤ 357072941)
    (by decide : 357072941 ≤ 357105709) block0 block1

theorem join_0_1 : (twinPrimeSegment 357105709 357171245).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 357105709 ≤ 357138477)
    (by decide : 357138477 ≤ 357171245) block2 block3

theorem join_1_0 : (twinPrimeSegment 357040173 357171245).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 357040173 ≤ 357105709)
    (by decide : 357105709 ≤ 357171245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 357040173 357171245).card = 459 := join_1_0

end S170C04
end Sude.GeneratedTwinScan
