import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12821)) 164364333 164397101 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 164364333 164397101).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12821 164364333 164397101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12823)) 164397101 164429869 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 164397101 164429869).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12823 164397101 164429869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12824)) 164429869 164462637 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 164429869 164462637).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12824 164429869 164462637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12825)) 164462637 164495405 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 164462637 164495405).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12825 164462637 164495405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 164364333 164429869).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 164364333 ≤ 164397101)
    (by decide : 164397101 ≤ 164429869) block0 block1

theorem join_0_1 : (twinPrimeSegment 164429869 164495405).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 164429869 ≤ 164462637)
    (by decide : 164462637 ≤ 164495405) block2 block3

theorem join_1_0 : (twinPrimeSegment 164364333 164495405).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 164364333 ≤ 164429869)
    (by decide : 164429869 ≤ 164495405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 164364333 164495405).card = 487 := join_1_0

end S078C06
end Sude.GeneratedTwinScan
