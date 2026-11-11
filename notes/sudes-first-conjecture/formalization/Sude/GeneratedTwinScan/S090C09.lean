import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13782)) 189923373 189956141 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 189923373 189956141).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13782 189923373 189956141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13783)) 189956141 189988909 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 189956141 189988909).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13783 189956141 189988909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13784)) 189988909 190021677 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 189988909 190021677).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13784 189988909 190021677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13786)) 190021677 190054445 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 190021677 190054445).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13786 190021677 190054445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 189923373 189988909).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 189923373 ≤ 189956141)
    (by decide : 189956141 ≤ 189988909) block0 block1

theorem join_0_1 : (twinPrimeSegment 189988909 190054445).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 189988909 ≤ 190021677)
    (by decide : 190021677 ≤ 190054445) block2 block3

theorem join_1_0 : (twinPrimeSegment 189923373 190054445).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 189923373 ≤ 189988909)
    (by decide : 189988909 ≤ 190054445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 189923373 190054445).card = 507 := join_1_0

end S090C09
end Sude.GeneratedTwinScan
