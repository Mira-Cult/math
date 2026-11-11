import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19321)) 373293101 373325869 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 373293101 373325869).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19321 373293101 373325869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19322)) 373325869 373358637 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 373325869 373358637).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19322 373325869 373358637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19323)) 373358637 373391405 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 373358637 373391405).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19323 373358637 373391405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19324)) 373391405 373424173 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 373391405 373424173).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19324 373391405 373424173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 373293101 373358637).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 373293101 ≤ 373325869)
    (by decide : 373325869 ≤ 373358637) block0 block1

theorem join_0_1 : (twinPrimeSegment 373358637 373424173).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 373358637 ≤ 373391405)
    (by decide : 373391405 ≤ 373424173) block2 block3

theorem join_1_0 : (twinPrimeSegment 373293101 373424173).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 373293101 ≤ 373358637)
    (by decide : 373358637 ≤ 373424173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 373293101 373424173).card = 422 := join_1_0

end S178C00
end Sude.GeneratedTwinScan
