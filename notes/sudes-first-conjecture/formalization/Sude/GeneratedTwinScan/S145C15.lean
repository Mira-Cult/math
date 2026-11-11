import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17495)) 306053165 306085933 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 306053165 306085933).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17495 306053165 306085933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17496)) 306085933 306118701 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 306085933 306118701).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17496 306085933 306118701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17497)) 306118701 306151469 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 306118701 306151469).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17497 306118701 306151469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17498)) 306151469 306184237 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 306151469 306184237).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17498 306151469 306184237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 306053165 306118701).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 306053165 ≤ 306085933)
    (by decide : 306085933 ≤ 306118701) block0 block1

theorem join_0_1 : (twinPrimeSegment 306118701 306184237).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 306118701 ≤ 306151469)
    (by decide : 306151469 ≤ 306184237) block2 block3

theorem join_1_0 : (twinPrimeSegment 306053165 306184237).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 306053165 ≤ 306118701)
    (by decide : 306118701 ≤ 306184237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 306053165 306184237).card = 491 := join_1_0

end S145C15
end Sude.GeneratedTwinScan
