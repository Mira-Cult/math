import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13629)) 185729069 185761837 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 185729069 185761837).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13629 185729069 185761837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13630)) 185761837 185794605 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 185761837 185794605).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13630 185761837 185794605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13631)) 185794605 185827373 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 185794605 185827373).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13631 185794605 185827373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13633)) 185827373 185860141 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 185827373 185860141).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13633 185827373 185860141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 185729069 185794605).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 185729069 ≤ 185761837)
    (by decide : 185761837 ≤ 185794605) block0 block1

theorem join_0_1 : (twinPrimeSegment 185794605 185860141).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 185794605 ≤ 185827373)
    (by decide : 185827373 ≤ 185860141) block2 block3

theorem join_1_0 : (twinPrimeSegment 185729069 185860141).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 185729069 ≤ 185794605)
    (by decide : 185794605 ≤ 185860141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 185729069 185860141).card = 471 := join_1_0

end S088C09
end Sude.GeneratedTwinScan
