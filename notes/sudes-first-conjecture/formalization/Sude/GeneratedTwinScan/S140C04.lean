import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17151)) 294125613 294158381 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 294125613 294158381).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17151 294125613 294158381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17152)) 294158381 294191149 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 294158381 294191149).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17152 294158381 294191149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17152)) 294191149 294223917 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 294191149 294223917).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17152 294191149 294223917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17153)) 294223917 294256685 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 294223917 294256685).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17153 294223917 294256685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 294125613 294191149).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 294125613 ≤ 294158381)
    (by decide : 294158381 ≤ 294191149) block0 block1

theorem join_0_1 : (twinPrimeSegment 294191149 294256685).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 294191149 ≤ 294223917)
    (by decide : 294223917 ≤ 294256685) block2 block3

theorem join_1_0 : (twinPrimeSegment 294125613 294256685).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 294125613 ≤ 294191149)
    (by decide : 294191149 ≤ 294256685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 294125613 294256685).card = 466 := join_1_0

end S140C04
end Sude.GeneratedTwinScan
