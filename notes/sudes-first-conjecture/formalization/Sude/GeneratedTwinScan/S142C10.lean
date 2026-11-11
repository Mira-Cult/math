import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17295)) 299106349 299139117 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 299106349 299139117).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17295 299106349 299139117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17296)) 299139117 299171885 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 299139117 299171885).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17296 299139117 299171885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17297)) 299171885 299204653 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 299171885 299204653).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17297 299171885 299204653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17298)) 299204653 299237421 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 299204653 299237421).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17298 299204653 299237421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 299106349 299171885).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 299106349 ≤ 299139117)
    (by decide : 299139117 ≤ 299171885) block0 block1

theorem join_0_1 : (twinPrimeSegment 299171885 299237421).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 299171885 ≤ 299204653)
    (by decide : 299204653 ≤ 299237421) block2 block3

theorem join_1_0 : (twinPrimeSegment 299106349 299237421).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 299106349 ≤ 299171885)
    (by decide : 299171885 ≤ 299237421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 299106349 299237421).card = 454 := join_1_0

end S142C10
end Sude.GeneratedTwinScan
