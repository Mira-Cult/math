import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22144)) 490340397 490373165 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 490340397 490373165).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22144 490340397 490373165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22145)) 490373165 490405933 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 490373165 490405933).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22145 490373165 490405933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22145)) 490405933 490438701 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 490405933 490438701).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22145 490405933 490438701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22146)) 490438701 490471469 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 490438701 490471469).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22146 490438701 490471469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 490340397 490405933).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 490340397 ≤ 490373165)
    (by decide : 490373165 ≤ 490405933) block0 block1

theorem join_0_1 : (twinPrimeSegment 490405933 490471469).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 490405933 ≤ 490438701)
    (by decide : 490438701 ≤ 490471469) block2 block3

theorem join_1_0 : (twinPrimeSegment 490340397 490471469).card = 398 := by
  simpa using combineTwinPrimeSegments (by decide : 490340397 ≤ 490405933)
    (by decide : 490405933 ≤ 490471469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 490340397 490471469).card = 398 := join_1_0

end S233C13
end Sude.GeneratedTwinScan
