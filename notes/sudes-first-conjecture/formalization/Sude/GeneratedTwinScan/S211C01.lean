import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21039)) 442630189 442662957 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 442630189 442662957).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21039 442630189 442662957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21040)) 442662957 442695725 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 442662957 442695725).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21040 442662957 442695725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21041)) 442695725 442728493 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 442695725 442728493).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21041 442695725 442728493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21041)) 442728493 442761261 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 442728493 442761261).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21041 442728493 442761261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 442630189 442695725).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 442630189 ≤ 442662957)
    (by decide : 442662957 ≤ 442695725) block0 block1

theorem join_0_1 : (twinPrimeSegment 442695725 442761261).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 442695725 ≤ 442728493)
    (by decide : 442728493 ≤ 442761261) block2 block3

theorem join_1_0 : (twinPrimeSegment 442630189 442761261).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 442630189 ≤ 442695725)
    (by decide : 442695725 ≤ 442761261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 442630189 442761261).card = 442 := join_1_0

end S211C01
end Sude.GeneratedTwinScan
