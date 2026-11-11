import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12521)) 156762157 156794925 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 156762157 156794925).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12521 156762157 156794925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12523)) 156794925 156827693 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 156794925 156827693).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12523 156794925 156827693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12524)) 156827693 156860461 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 156827693 156860461).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12524 156827693 156860461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12525)) 156860461 156893229 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 156860461 156893229).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12525 156860461 156893229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 156762157 156827693).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 156762157 ≤ 156794925)
    (by decide : 156794925 ≤ 156827693) block0 block1

theorem join_0_1 : (twinPrimeSegment 156827693 156893229).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 156827693 ≤ 156860461)
    (by decide : 156860461 ≤ 156893229) block2 block3

theorem join_1_0 : (twinPrimeSegment 156762157 156893229).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 156762157 ≤ 156827693)
    (by decide : 156827693 ≤ 156893229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 156762157 156893229).card = 491 := join_1_0

end S074C12
end Sude.GeneratedTwinScan
