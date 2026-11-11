import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15137)) 229113901 229146669 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 229113901 229146669).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15137 229113901 229146669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15138)) 229146669 229179437 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 229146669 229179437).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15138 229146669 229179437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15139)) 229179437 229212205 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 229179437 229212205).card = 147 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15139 229179437 229212205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15140)) 229212205 229244973 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 229212205 229244973).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15140 229212205 229244973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 229113901 229179437).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 229113901 ≤ 229146669)
    (by decide : 229146669 ≤ 229179437) block0 block1

theorem join_0_1 : (twinPrimeSegment 229179437 229244973).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 229179437 ≤ 229212205)
    (by decide : 229212205 ≤ 229244973) block2 block3

theorem join_1_0 : (twinPrimeSegment 229113901 229244973).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 229113901 ≤ 229179437)
    (by decide : 229179437 ≤ 229244973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 229113901 229244973).card = 483 := join_1_0

end S109C04
end Sude.GeneratedTwinScan
