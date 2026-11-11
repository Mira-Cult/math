import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20902)) 436863021 436895789 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 436863021 436895789).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20902 436863021 436895789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20902)) 436895789 436928557 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 436895789 436928557).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20902 436895789 436928557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20903)) 436928557 436961325 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 436928557 436961325).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20903 436928557 436961325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20904)) 436961325 436994093 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 436961325 436994093).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20904 436961325 436994093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 436863021 436928557).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 436863021 ≤ 436895789)
    (by decide : 436895789 ≤ 436928557) block0 block1

theorem join_0_1 : (twinPrimeSegment 436928557 436994093).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 436928557 ≤ 436961325)
    (by decide : 436961325 ≤ 436994093) block2 block3

theorem join_1_0 : (twinPrimeSegment 436863021 436994093).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 436863021 ≤ 436928557)
    (by decide : 436928557 ≤ 436994093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 436863021 436994093).card = 427 := join_1_0

end S208C05
end Sude.GeneratedTwinScan
