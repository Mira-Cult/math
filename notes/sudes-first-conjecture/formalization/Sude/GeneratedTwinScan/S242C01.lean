import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22531)) 507641901 507674669 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 507641901 507674669).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22531 507641901 507674669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22532)) 507674669 507707437 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 507674669 507707437).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22532 507674669 507707437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22533)) 507707437 507740205 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 507707437 507740205).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22533 507707437 507740205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22533)) 507740205 507772973 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 507740205 507772973).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22533 507740205 507772973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 507641901 507707437).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 507641901 ≤ 507674669)
    (by decide : 507674669 ≤ 507707437) block0 block1

theorem join_0_1 : (twinPrimeSegment 507707437 507772973).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 507707437 ≤ 507740205)
    (by decide : 507740205 ≤ 507772973) block2 block3

theorem join_1_0 : (twinPrimeSegment 507641901 507772973).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 507641901 ≤ 507707437)
    (by decide : 507707437 ≤ 507772973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 507641901 507772973).card = 433 := join_1_0

end S242C01
end Sude.GeneratedTwinScan
