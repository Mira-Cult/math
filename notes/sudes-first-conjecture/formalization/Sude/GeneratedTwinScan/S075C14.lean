import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12615)) 159121453 159154221 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 159121453 159154221).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12615 159121453 159154221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12616)) 159154221 159186989 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 159154221 159186989).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12616 159154221 159186989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12618)) 159186989 159219757 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 159186989 159219757).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12618 159186989 159219757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12619)) 159219757 159252525 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 159219757 159252525).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12619 159219757 159252525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 159121453 159186989).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 159121453 ≤ 159154221)
    (by decide : 159154221 ≤ 159186989) block0 block1

theorem join_0_1 : (twinPrimeSegment 159186989 159252525).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 159186989 ≤ 159219757)
    (by decide : 159219757 ≤ 159252525) block2 block3

theorem join_1_0 : (twinPrimeSegment 159121453 159252525).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 159121453 ≤ 159186989)
    (by decide : 159186989 ≤ 159252525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 159121453 159252525).card = 491 := join_1_0

end S075C14
end Sude.GeneratedTwinScan
