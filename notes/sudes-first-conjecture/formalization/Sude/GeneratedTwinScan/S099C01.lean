import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14414)) 207749165 207781933 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 207749165 207781933).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14414 207749165 207781933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14415)) 207781933 207814701 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 207781933 207814701).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14415 207781933 207814701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14416)) 207814701 207847469 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 207814701 207847469).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14416 207814701 207847469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14418)) 207847469 207880237 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 207847469 207880237).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14418 207847469 207880237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 207749165 207814701).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 207749165 ≤ 207781933)
    (by decide : 207781933 ≤ 207814701) block0 block1

theorem join_0_1 : (twinPrimeSegment 207814701 207880237).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 207814701 ≤ 207847469)
    (by decide : 207847469 ≤ 207880237) block2 block3

theorem join_1_0 : (twinPrimeSegment 207749165 207880237).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 207749165 ≤ 207814701)
    (by decide : 207814701 ≤ 207880237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 207749165 207880237).card = 490 := join_1_0

end S099C01
end Sude.GeneratedTwinScan
