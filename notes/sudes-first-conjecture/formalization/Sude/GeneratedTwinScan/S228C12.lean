import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21903)) 479723565 479756333 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 479723565 479756333).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21903 479723565 479756333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21904)) 479756333 479789101 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 479756333 479789101).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21904 479756333 479789101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21904)) 479789101 479821869 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 479789101 479821869).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21904 479789101 479821869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21905)) 479821869 479854637 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 479821869 479854637).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21905 479821869 479854637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 479723565 479789101).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 479723565 ≤ 479756333)
    (by decide : 479756333 ≤ 479789101) block0 block1

theorem join_0_1 : (twinPrimeSegment 479789101 479854637).card = 189 := by
  simpa using combineTwinPrimeSegments (by decide : 479789101 ≤ 479821869)
    (by decide : 479821869 ≤ 479854637) block2 block3

theorem join_1_0 : (twinPrimeSegment 479723565 479854637).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 479723565 ≤ 479789101)
    (by decide : 479789101 ≤ 479854637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 479723565 479854637).card = 427 := join_1_0

end S228C12
end Sude.GeneratedTwinScan
