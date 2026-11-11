import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19567)) 382861357 382894125 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 382861357 382894125).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19567 382861357 382894125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19568)) 382894125 382926893 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 382894125 382926893).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19568 382894125 382926893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19569)) 382926893 382959661 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 382926893 382959661).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19569 382926893 382959661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19570)) 382959661 382992429 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 382959661 382992429).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19570 382959661 382992429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 382861357 382926893).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 382861357 ≤ 382894125)
    (by decide : 382894125 ≤ 382926893) block0 block1

theorem join_0_1 : (twinPrimeSegment 382926893 382992429).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 382926893 ≤ 382959661)
    (by decide : 382959661 ≤ 382992429) block2 block3

theorem join_1_0 : (twinPrimeSegment 382861357 382992429).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 382861357 ≤ 382926893)
    (by decide : 382926893 ≤ 382992429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 382861357 382992429).card = 466 := join_1_0

end S182C09
end Sude.GeneratedTwinScan
