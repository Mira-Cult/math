import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20754)) 430702637 430735405 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 430702637 430735405).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20754 430702637 430735405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20754)) 430735405 430768173 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 430735405 430768173).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20754 430735405 430768173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20755)) 430768173 430800941 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 430768173 430800941).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20755 430768173 430800941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20756)) 430800941 430833709 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 430800941 430833709).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20756 430800941 430833709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 430702637 430768173).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 430702637 ≤ 430735405)
    (by decide : 430735405 ≤ 430768173) block0 block1

theorem join_0_1 : (twinPrimeSegment 430768173 430833709).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 430768173 ≤ 430800941)
    (by decide : 430800941 ≤ 430833709) block2 block3

theorem join_1_0 : (twinPrimeSegment 430702637 430833709).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 430702637 ≤ 430768173)
    (by decide : 430768173 ≤ 430833709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 430702637 430833709).card = 425 := join_1_0

end S205C06
end Sude.GeneratedTwinScan
