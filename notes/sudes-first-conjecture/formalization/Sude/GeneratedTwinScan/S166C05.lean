import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18676)) 348782637 348815405 = 94 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 348782637 348815405).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18676 348782637 348815405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18677)) 348815405 348848173 = 84 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 348815405 348848173).card = 84 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18677 348815405 348848173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18678)) 348848173 348880941 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 348848173 348880941).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18678 348848173 348880941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18679)) 348880941 348913709 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 348880941 348913709).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18679 348880941 348913709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 348782637 348848173).card = 178 := by
  simpa using combineTwinPrimeSegments (by decide : 348782637 ≤ 348815405)
    (by decide : 348815405 ≤ 348848173) block0 block1

theorem join_0_1 : (twinPrimeSegment 348848173 348913709).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 348848173 ≤ 348880941)
    (by decide : 348880941 ≤ 348913709) block2 block3

theorem join_1_0 : (twinPrimeSegment 348782637 348913709).card = 389 := by
  simpa using combineTwinPrimeSegments (by decide : 348782637 ≤ 348848173)
    (by decide : 348848173 ≤ 348913709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 348782637 348913709).card = 389 := join_1_0

end S166C05
end Sude.GeneratedTwinScan
