import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14213)) 201981997 202014765 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 201981997 202014765).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14213 201981997 202014765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14214)) 202014765 202047533 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 202014765 202047533).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14214 202014765 202047533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14215)) 202047533 202080301 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 202047533 202080301).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14215 202047533 202080301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14216)) 202080301 202113069 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 202080301 202113069).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14216 202080301 202113069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 201981997 202047533).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 201981997 ≤ 202014765)
    (by decide : 202014765 ≤ 202047533) block0 block1

theorem join_0_1 : (twinPrimeSegment 202047533 202113069).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 202047533 ≤ 202080301)
    (by decide : 202080301 ≤ 202113069) block2 block3

theorem join_1_0 : (twinPrimeSegment 201981997 202113069).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 201981997 ≤ 202047533)
    (by decide : 202047533 ≤ 202113069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 201981997 202113069).card = 470 := join_1_0

end S096C05
end Sude.GeneratedTwinScan
