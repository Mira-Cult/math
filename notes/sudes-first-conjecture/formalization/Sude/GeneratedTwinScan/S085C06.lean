import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13381)) 179044397 179077165 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 179044397 179077165).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13381 179044397 179077165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13383)) 179077165 179109933 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 179077165 179109933).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13383 179077165 179109933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13384)) 179109933 179142701 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 179109933 179142701).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13384 179109933 179142701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13385)) 179142701 179175469 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 179142701 179175469).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13385 179142701 179175469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 179044397 179109933).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 179044397 ≤ 179077165)
    (by decide : 179077165 ≤ 179109933) block0 block1

theorem join_0_1 : (twinPrimeSegment 179109933 179175469).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 179109933 ≤ 179142701)
    (by decide : 179142701 ≤ 179175469) block2 block3

theorem join_1_0 : (twinPrimeSegment 179044397 179175469).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 179044397 ≤ 179109933)
    (by decide : 179109933 ≤ 179175469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 179044397 179175469).card = 463 := join_1_0

end S085C06
end Sude.GeneratedTwinScan
