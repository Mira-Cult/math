import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17431)) 303824941 303857709 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 303824941 303857709).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17431 303824941 303857709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17432)) 303857709 303890477 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 303857709 303890477).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17432 303857709 303890477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17433)) 303890477 303923245 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 303890477 303923245).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17433 303890477 303923245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17434)) 303923245 303956013 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 303923245 303956013).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17434 303923245 303956013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 303824941 303890477).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 303824941 ≤ 303857709)
    (by decide : 303857709 ≤ 303890477) block0 block1

theorem join_0_1 : (twinPrimeSegment 303890477 303956013).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 303890477 ≤ 303923245)
    (by decide : 303923245 ≤ 303956013) block2 block3

theorem join_1_0 : (twinPrimeSegment 303824941 303956013).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 303824941 ≤ 303890477)
    (by decide : 303890477 ≤ 303956013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 303824941 303956013).card = 481 := join_1_0

end S144C14
end Sude.GeneratedTwinScan
