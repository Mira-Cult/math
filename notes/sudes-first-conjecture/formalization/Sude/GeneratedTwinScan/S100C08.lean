import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14518)) 210763821 210796589 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 210763821 210796589).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14518 210763821 210796589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14519)) 210796589 210829357 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 210796589 210829357).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14519 210796589 210829357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14521)) 210829357 210862125 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 210829357 210862125).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14521 210829357 210862125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14522)) 210862125 210894893 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 210862125 210894893).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14522 210862125 210894893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 210763821 210829357).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 210763821 ≤ 210796589)
    (by decide : 210796589 ≤ 210829357) block0 block1

theorem join_0_1 : (twinPrimeSegment 210829357 210894893).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 210829357 ≤ 210862125)
    (by decide : 210862125 ≤ 210894893) block2 block3

theorem join_1_0 : (twinPrimeSegment 210763821 210894893).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 210763821 ≤ 210829357)
    (by decide : 210829357 ≤ 210894893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 210763821 210894893).card = 450 := join_1_0

end S100C08
end Sude.GeneratedTwinScan
