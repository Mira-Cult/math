import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13034)) 169869357 169902125 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 169869357 169902125).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13034 169869357 169902125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13035)) 169902125 169934893 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 169902125 169934893).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13035 169902125 169934893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13037)) 169934893 169967661 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 169934893 169967661).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13037 169934893 169967661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13038)) 169967661 170000429 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 169967661 170000429).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13038 169967661 170000429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 169869357 169934893).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 169869357 ≤ 169902125)
    (by decide : 169902125 ≤ 169934893) block0 block1

theorem join_0_1 : (twinPrimeSegment 169934893 170000429).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 169934893 ≤ 169967661)
    (by decide : 169967661 ≤ 170000429) block2 block3

theorem join_1_0 : (twinPrimeSegment 169869357 170000429).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 169869357 ≤ 169934893)
    (by decide : 169934893 ≤ 170000429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 169869357 170000429).card = 480 := join_1_0

end S081C00
end Sude.GeneratedTwinScan
