import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12979)) 168427565 168460333 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 168427565 168460333).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12979 168427565 168460333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12980)) 168460333 168493101 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 168460333 168493101).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12980 168460333 168493101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12981)) 168493101 168525869 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 168493101 168525869).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12981 168493101 168525869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12983)) 168525869 168558637 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 168525869 168558637).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12983 168525869 168558637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 168427565 168493101).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 168427565 ≤ 168460333)
    (by decide : 168460333 ≤ 168493101) block0 block1

theorem join_0_1 : (twinPrimeSegment 168493101 168558637).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 168493101 ≤ 168525869)
    (by decide : 168525869 ≤ 168558637) block2 block3

theorem join_1_0 : (twinPrimeSegment 168427565 168558637).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 168427565 ≤ 168493101)
    (by decide : 168493101 ≤ 168558637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 168427565 168558637).card = 473 := join_1_0

end S080C05
end Sude.GeneratedTwinScan
