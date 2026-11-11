import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16682)) 278265901 278298669 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 278265901 278298669).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16682 278265901 278298669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16683)) 278298669 278331437 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 278298669 278331437).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16683 278298669 278331437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16684)) 278331437 278364205 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 278331437 278364205).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16684 278331437 278364205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16685)) 278364205 278396973 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 278364205 278396973).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16685 278364205 278396973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 278265901 278331437).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 278265901 ≤ 278298669)
    (by decide : 278298669 ≤ 278331437) block0 block1

theorem join_0_1 : (twinPrimeSegment 278331437 278396973).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 278331437 ≤ 278364205)
    (by decide : 278364205 ≤ 278396973) block2 block3

theorem join_1_0 : (twinPrimeSegment 278265901 278396973).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 278265901 ≤ 278331437)
    (by decide : 278331437 ≤ 278396973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 278265901 278396973).card = 462 := join_1_0

end S132C11
end Sude.GeneratedTwinScan
