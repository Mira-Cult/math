import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12657)) 160170029 160202797 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 160170029 160202797).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12657 160170029 160202797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12658)) 160202797 160235565 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 160202797 160235565).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12658 160202797 160235565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12659)) 160235565 160268333 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 160235565 160268333).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12659 160235565 160268333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12661)) 160268333 160301101 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 160268333 160301101).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12661 160268333 160301101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 160170029 160235565).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 160170029 ≤ 160202797)
    (by decide : 160202797 ≤ 160235565) block0 block1

theorem join_0_1 : (twinPrimeSegment 160235565 160301101).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 160235565 ≤ 160268333)
    (by decide : 160268333 ≤ 160301101) block2 block3

theorem join_1_0 : (twinPrimeSegment 160170029 160301101).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 160170029 ≤ 160235565)
    (by decide : 160235565 ≤ 160301101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 160170029 160301101).card = 481 := join_1_0

end S076C06
end Sude.GeneratedTwinScan
