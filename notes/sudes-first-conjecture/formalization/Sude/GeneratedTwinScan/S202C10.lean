import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20614)) 424935469 424968237 = 90 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 424935469 424968237).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20614 424935469 424968237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20615)) 424968237 425001005 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 424968237 425001005).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20615 424968237 425001005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20616)) 425001005 425033773 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 425001005 425033773).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20616 425001005 425033773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20617)) 425033773 425066541 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 425033773 425066541).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20617 425033773 425066541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 424935469 425001005).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 424935469 ≤ 424968237)
    (by decide : 424968237 ≤ 425001005) block0 block1

theorem join_0_1 : (twinPrimeSegment 425001005 425066541).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 425001005 ≤ 425033773)
    (by decide : 425033773 ≤ 425066541) block2 block3

theorem join_1_0 : (twinPrimeSegment 424935469 425066541).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 424935469 ≤ 425001005)
    (by decide : 425001005 ≤ 425066541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 424935469 425066541).card = 424 := join_1_0

end S202C10
end Sude.GeneratedTwinScan
