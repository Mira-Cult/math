import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12568)) 157941805 157974573 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 157941805 157974573).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12568 157941805 157974573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12570)) 157974573 158007341 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 157974573 158007341).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12570 157974573 158007341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12571)) 158007341 158040109 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 158007341 158040109).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12571 158007341 158040109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12572)) 158040109 158072877 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 158040109 158072877).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12572 158040109 158072877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 157941805 158007341).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 157941805 ≤ 157974573)
    (by decide : 157974573 ≤ 158007341) block0 block1

theorem join_0_1 : (twinPrimeSegment 158007341 158072877).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 158007341 ≤ 158040109)
    (by decide : 158040109 ≤ 158072877) block2 block3

theorem join_1_0 : (twinPrimeSegment 157941805 158072877).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 157941805 ≤ 158007341)
    (by decide : 158007341 ≤ 158072877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 157941805 158072877).card = 487 := join_1_0

end S075C05
end Sude.GeneratedTwinScan
