import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15897)) 252706861 252739629 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 252706861 252739629).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15897 252706861 252739629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15898)) 252739629 252772397 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 252739629 252772397).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15898 252739629 252772397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15899)) 252772397 252805165 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 252772397 252805165).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15899 252772397 252805165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15900)) 252805165 252837933 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 252805165 252837933).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15900 252805165 252837933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 252706861 252772397).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 252706861 ≤ 252739629)
    (by decide : 252739629 ≤ 252772397) block0 block1

theorem join_0_1 : (twinPrimeSegment 252772397 252837933).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 252772397 ≤ 252805165)
    (by decide : 252805165 ≤ 252837933) block2 block3

theorem join_1_0 : (twinPrimeSegment 252706861 252837933).card = 515 := by
  simpa using combineTwinPrimeSegments (by decide : 252706861 ≤ 252772397)
    (by decide : 252772397 ≤ 252837933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 252706861 252837933).card = 515 := join_1_0

end S120C08
end Sude.GeneratedTwinScan
