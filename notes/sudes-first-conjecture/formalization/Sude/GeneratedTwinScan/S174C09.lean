import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19134)) 366084141 366116909 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 366084141 366116909).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19134 366084141 366116909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19135)) 366116909 366149677 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 366116909 366149677).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19135 366116909 366149677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19135)) 366149677 366182445 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 366149677 366182445).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19135 366149677 366182445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19136)) 366182445 366215213 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 366182445 366215213).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19136 366182445 366215213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 366084141 366149677).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 366084141 ≤ 366116909)
    (by decide : 366116909 ≤ 366149677) block0 block1

theorem join_0_1 : (twinPrimeSegment 366149677 366215213).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 366149677 ≤ 366182445)
    (by decide : 366182445 ≤ 366215213) block2 block3

theorem join_1_0 : (twinPrimeSegment 366084141 366215213).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 366084141 ≤ 366149677)
    (by decide : 366149677 ≤ 366215213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 366084141 366215213).card = 457 := join_1_0

end S174C09
end Sude.GeneratedTwinScan
