import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13396)) 179437613 179470381 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 179437613 179470381).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13396 179437613 179470381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13397)) 179470381 179503149 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 179470381 179503149).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13397 179470381 179503149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13399)) 179503149 179535917 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 179503149 179535917).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13399 179503149 179535917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13400)) 179535917 179568685 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 179535917 179568685).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13400 179535917 179568685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 179437613 179503149).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 179437613 ≤ 179470381)
    (by decide : 179470381 ≤ 179503149) block0 block1

theorem join_0_1 : (twinPrimeSegment 179503149 179568685).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 179503149 ≤ 179535917)
    (by decide : 179535917 ≤ 179568685) block2 block3

theorem join_1_0 : (twinPrimeSegment 179437613 179568685).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 179437613 ≤ 179503149)
    (by decide : 179503149 ≤ 179568685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 179437613 179568685).card = 475 := join_1_0

end S085C09
end Sude.GeneratedTwinScan
