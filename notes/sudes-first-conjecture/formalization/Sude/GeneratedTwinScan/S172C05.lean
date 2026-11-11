import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19010)) 361365549 361398317 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 361365549 361398317).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19010 361365549 361398317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19011)) 361398317 361431085 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 361398317 361431085).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19011 361398317 361431085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19012)) 361431085 361463853 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 361431085 361463853).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19012 361431085 361463853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19013)) 361463853 361496621 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 361463853 361496621).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19013 361463853 361496621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 361365549 361431085).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 361365549 ≤ 361398317)
    (by decide : 361398317 ≤ 361431085) block0 block1

theorem join_0_1 : (twinPrimeSegment 361431085 361496621).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 361431085 ≤ 361463853)
    (by decide : 361463853 ≤ 361496621) block2 block3

theorem join_1_0 : (twinPrimeSegment 361365549 361496621).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 361365549 ≤ 361431085)
    (by decide : 361431085 ≤ 361496621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 361365549 361496621).card = 459 := join_1_0

end S172C05
end Sude.GeneratedTwinScan
