import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15769)) 248643629 248676397 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 248643629 248676397).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15769 248643629 248676397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15770)) 248676397 248709165 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 248676397 248709165).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15770 248676397 248709165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15771)) 248709165 248741933 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 248709165 248741933).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15771 248709165 248741933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15772)) 248741933 248774701 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 248741933 248774701).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15772 248741933 248774701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 248643629 248709165).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 248643629 ≤ 248676397)
    (by decide : 248676397 ≤ 248709165) block0 block1

theorem join_0_1 : (twinPrimeSegment 248709165 248774701).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 248709165 ≤ 248741933)
    (by decide : 248741933 ≤ 248774701) block2 block3

theorem join_1_0 : (twinPrimeSegment 248643629 248774701).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 248643629 ≤ 248709165)
    (by decide : 248709165 ≤ 248774701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 248643629 248774701).card = 468 := join_1_0

end S118C09
end Sude.GeneratedTwinScan
