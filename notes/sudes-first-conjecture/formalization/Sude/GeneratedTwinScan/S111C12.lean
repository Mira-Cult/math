import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15309)) 234356781 234389549 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 234356781 234389549).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15309 234356781 234389549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15310)) 234389549 234422317 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 234389549 234422317).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15310 234389549 234422317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15311)) 234422317 234455085 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 234422317 234455085).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15311 234422317 234455085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15312)) 234455085 234487853 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 234455085 234487853).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15312 234455085 234487853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 234356781 234422317).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 234356781 ≤ 234389549)
    (by decide : 234389549 ≤ 234422317) block0 block1

theorem join_0_1 : (twinPrimeSegment 234422317 234487853).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 234422317 ≤ 234455085)
    (by decide : 234455085 ≤ 234487853) block2 block3

theorem join_1_0 : (twinPrimeSegment 234356781 234487853).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 234356781 ≤ 234422317)
    (by decide : 234422317 ≤ 234487853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 234356781 234487853).card = 481 := join_1_0

end S111C12
end Sude.GeneratedTwinScan
