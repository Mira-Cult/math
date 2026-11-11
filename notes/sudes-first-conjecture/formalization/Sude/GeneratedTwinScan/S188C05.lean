import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19873)) 394919981 394952749 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 394919981 394952749).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19873 394919981 394952749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19874)) 394952749 394985517 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 394952749 394985517).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19874 394952749 394985517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19875)) 394985517 395018285 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 394985517 395018285).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19875 394985517 395018285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19875)) 395018285 395051053 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 395018285 395051053).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19875 395018285 395051053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 394919981 394985517).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 394919981 ≤ 394952749)
    (by decide : 394952749 ≤ 394985517) block0 block1

theorem join_0_1 : (twinPrimeSegment 394985517 395051053).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 394985517 ≤ 395018285)
    (by decide : 395018285 ≤ 395051053) block2 block3

theorem join_1_0 : (twinPrimeSegment 394919981 395051053).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 394919981 ≤ 394985517)
    (by decide : 394985517 ≤ 395051053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 394919981 395051053).card = 451 := join_1_0

end S188C05
end Sude.GeneratedTwinScan
