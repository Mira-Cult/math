import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17047)) 290586669 290619437 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 290586669 290619437).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17047 290586669 290619437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17048)) 290619437 290652205 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 290619437 290652205).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17048 290619437 290652205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17049)) 290652205 290684973 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 290652205 290684973).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17049 290652205 290684973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17050)) 290684973 290717741 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 290684973 290717741).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17050 290684973 290717741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 290586669 290652205).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 290586669 ≤ 290619437)
    (by decide : 290619437 ≤ 290652205) block0 block1

theorem join_0_1 : (twinPrimeSegment 290652205 290717741).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 290652205 ≤ 290684973)
    (by decide : 290684973 ≤ 290717741) block2 block3

theorem join_1_0 : (twinPrimeSegment 290586669 290717741).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 290586669 ≤ 290652205)
    (by decide : 290652205 ≤ 290717741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 290586669 290717741).card = 484 := join_1_0

end S138C09
end Sude.GeneratedTwinScan
