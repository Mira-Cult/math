import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12831)) 164626477 164659245 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 164626477 164659245).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12831 164626477 164659245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12833)) 164659245 164692013 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 164659245 164692013).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12833 164659245 164692013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12834)) 164692013 164724781 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 164692013 164724781).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12834 164692013 164724781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12835)) 164724781 164757549 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 164724781 164757549).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12835 164724781 164757549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 164626477 164692013).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 164626477 ≤ 164659245)
    (by decide : 164659245 ≤ 164692013) block0 block1

theorem join_0_1 : (twinPrimeSegment 164692013 164757549).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 164692013 ≤ 164724781)
    (by decide : 164724781 ≤ 164757549) block2 block3

theorem join_1_0 : (twinPrimeSegment 164626477 164757549).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 164626477 ≤ 164692013)
    (by decide : 164692013 ≤ 164757549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 164626477 164757549).card = 446 := join_1_0

end S078C08
end Sude.GeneratedTwinScan
