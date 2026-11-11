import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22096)) 488243245 488276013 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 488243245 488276013).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22096 488243245 488276013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22097)) 488276013 488308781 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 488276013 488308781).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22097 488276013 488308781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22098)) 488308781 488341549 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 488308781 488341549).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22098 488308781 488341549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22099)) 488341549 488374317 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 488341549 488374317).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22099 488341549 488374317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 488243245 488308781).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 488243245 ≤ 488276013)
    (by decide : 488276013 ≤ 488308781) block0 block1

theorem join_0_1 : (twinPrimeSegment 488308781 488374317).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 488308781 ≤ 488341549)
    (by decide : 488341549 ≤ 488374317) block2 block3

theorem join_1_0 : (twinPrimeSegment 488243245 488374317).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 488243245 ≤ 488308781)
    (by decide : 488308781 ≤ 488374317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 488243245 488374317).card = 425 := join_1_0

end S232C13
end Sude.GeneratedTwinScan
