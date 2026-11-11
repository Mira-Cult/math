import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15686)) 246022189 246054957 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 246022189 246054957).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15686 246022189 246054957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15687)) 246054957 246087725 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 246054957 246087725).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15687 246054957 246087725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15688)) 246087725 246120493 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 246087725 246120493).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15688 246087725 246120493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15689)) 246120493 246153261 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 246120493 246153261).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15689 246120493 246153261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 246022189 246087725).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 246022189 ≤ 246054957)
    (by decide : 246054957 ≤ 246087725) block0 block1

theorem join_0_1 : (twinPrimeSegment 246087725 246153261).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 246087725 ≤ 246120493)
    (by decide : 246120493 ≤ 246153261) block2 block3

theorem join_1_0 : (twinPrimeSegment 246022189 246153261).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 246022189 ≤ 246087725)
    (by decide : 246087725 ≤ 246153261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 246022189 246153261).card = 436 := join_1_0

end S117C05
end Sude.GeneratedTwinScan
