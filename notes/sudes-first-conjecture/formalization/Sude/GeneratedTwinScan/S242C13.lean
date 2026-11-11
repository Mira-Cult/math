import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22566)) 509214765 509247533 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 509214765 509247533).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22566 509214765 509247533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22567)) 509247533 509280301 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 509247533 509280301).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22567 509247533 509280301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22567)) 509280301 509313069 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 509280301 509313069).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22567 509280301 509313069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22568)) 509313069 509345837 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 509313069 509345837).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22568 509313069 509345837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 509214765 509280301).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 509214765 ≤ 509247533)
    (by decide : 509247533 ≤ 509280301) block0 block1

theorem join_0_1 : (twinPrimeSegment 509280301 509345837).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 509280301 ≤ 509313069)
    (by decide : 509313069 ≤ 509345837) block2 block3

theorem join_1_0 : (twinPrimeSegment 509214765 509345837).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 509214765 ≤ 509280301)
    (by decide : 509280301 ≤ 509345837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 509214765 509345837).card = 444 := join_1_0

end S242C13
end Sude.GeneratedTwinScan
