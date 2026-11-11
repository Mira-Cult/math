import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20810)) 433061933 433094701 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 433061933 433094701).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20810 433061933 433094701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20811)) 433094701 433127469 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 433094701 433127469).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20811 433094701 433127469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20812)) 433127469 433160237 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 433127469 433160237).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20812 433127469 433160237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20813)) 433160237 433193005 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 433160237 433193005).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20813 433160237 433193005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 433061933 433127469).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 433061933 ≤ 433094701)
    (by decide : 433094701 ≤ 433127469) block0 block1

theorem join_0_1 : (twinPrimeSegment 433127469 433193005).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 433127469 ≤ 433160237)
    (by decide : 433160237 ≤ 433193005) block2 block3

theorem join_1_0 : (twinPrimeSegment 433061933 433193005).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 433061933 ≤ 433127469)
    (by decide : 433127469 ≤ 433193005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 433061933 433193005).card = 426 := join_1_0

end S206C08
end Sude.GeneratedTwinScan
