import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18805)) 353632301 353665069 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 353632301 353665069).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18805 353632301 353665069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18806)) 353665069 353697837 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 353665069 353697837).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18806 353665069 353697837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18807)) 353697837 353730605 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 353697837 353730605).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18807 353697837 353730605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18808)) 353730605 353763373 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 353730605 353763373).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18808 353730605 353763373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 353632301 353697837).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 353632301 ≤ 353665069)
    (by decide : 353665069 ≤ 353697837) block0 block1

theorem join_0_1 : (twinPrimeSegment 353697837 353763373).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 353697837 ≤ 353730605)
    (by decide : 353730605 ≤ 353763373) block2 block3

theorem join_1_0 : (twinPrimeSegment 353632301 353763373).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 353632301 ≤ 353697837)
    (by decide : 353697837 ≤ 353763373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 353632301 353763373).card = 486 := join_1_0

end S168C10
end Sude.GeneratedTwinScan
