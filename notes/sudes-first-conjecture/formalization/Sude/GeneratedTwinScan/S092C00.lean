import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13891)) 192938029 192970797 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 192938029 192970797).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13891 192938029 192970797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13892)) 192970797 193003565 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 192970797 193003565).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13892 192970797 193003565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13893)) 193003565 193036333 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 193003565 193036333).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13893 193003565 193036333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13894)) 193036333 193069101 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 193036333 193069101).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13894 193036333 193069101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 192938029 193003565).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 192938029 ≤ 192970797)
    (by decide : 192970797 ≤ 193003565) block0 block1

theorem join_0_1 : (twinPrimeSegment 193003565 193069101).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 193003565 ≤ 193036333)
    (by decide : 193036333 ≤ 193069101) block2 block3

theorem join_1_0 : (twinPrimeSegment 192938029 193069101).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 192938029 ≤ 193003565)
    (by decide : 193003565 ≤ 193069101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 192938029 193069101).card = 465 := join_1_0

end S092C00
end Sude.GeneratedTwinScan
