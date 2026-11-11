import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14176)) 200933421 200966189 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 200933421 200966189).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14176 200933421 200966189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14177)) 200966189 200998957 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 200966189 200998957).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14177 200966189 200998957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14178)) 200998957 201031725 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 200998957 201031725).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14178 200998957 201031725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14179)) 201031725 201064493 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 201031725 201064493).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14179 201031725 201064493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 200933421 200998957).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 200933421 ≤ 200966189)
    (by decide : 200966189 ≤ 200998957) block0 block1

theorem join_0_1 : (twinPrimeSegment 200998957 201064493).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 200998957 ≤ 201031725)
    (by decide : 201031725 ≤ 201064493) block2 block3

theorem join_1_0 : (twinPrimeSegment 200933421 201064493).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 200933421 ≤ 200998957)
    (by decide : 200998957 ≤ 201064493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 200933421 201064493).card = 506 := join_1_0

end S095C13
end Sude.GeneratedTwinScan
