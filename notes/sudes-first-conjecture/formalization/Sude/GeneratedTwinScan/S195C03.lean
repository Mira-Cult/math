import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20232)) 409337901 409370669 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 409337901 409370669).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20232 409337901 409370669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20233)) 409370669 409403437 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 409370669 409403437).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20233 409370669 409403437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20234)) 409403437 409436205 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 409403437 409436205).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20234 409403437 409436205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20235)) 409436205 409468973 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 409436205 409468973).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20235 409436205 409468973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 409337901 409403437).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 409337901 ≤ 409370669)
    (by decide : 409370669 ≤ 409403437) block0 block1

theorem join_0_1 : (twinPrimeSegment 409403437 409468973).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 409403437 ≤ 409436205)
    (by decide : 409436205 ≤ 409468973) block2 block3

theorem join_1_0 : (twinPrimeSegment 409337901 409468973).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 409337901 ≤ 409403437)
    (by decide : 409403437 ≤ 409468973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 409337901 409468973).card = 420 := join_1_0

end S195C03
end Sude.GeneratedTwinScan
