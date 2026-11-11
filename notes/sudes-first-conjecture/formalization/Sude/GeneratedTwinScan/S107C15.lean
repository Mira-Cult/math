import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15046)) 226361389 226394157 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 226361389 226394157).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15046 226361389 226394157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15047)) 226394157 226426925 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 226394157 226426925).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15047 226394157 226426925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15048)) 226426925 226459693 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 226426925 226459693).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15048 226426925 226459693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15049)) 226459693 226492461 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 226459693 226492461).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15049 226459693 226492461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 226361389 226426925).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 226361389 ≤ 226394157)
    (by decide : 226394157 ≤ 226426925) block0 block1

theorem join_0_1 : (twinPrimeSegment 226426925 226492461).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 226426925 ≤ 226459693)
    (by decide : 226459693 ≤ 226492461) block2 block3

theorem join_1_0 : (twinPrimeSegment 226361389 226492461).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 226361389 ≤ 226426925)
    (by decide : 226426925 ≤ 226492461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 226361389 226492461).card = 488 := join_1_0

end S107C15
end Sude.GeneratedTwinScan
