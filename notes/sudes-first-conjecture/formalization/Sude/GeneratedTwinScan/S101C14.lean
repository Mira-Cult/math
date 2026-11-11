import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14617)) 213647405 213680173 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 213647405 213680173).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14617 213647405 213680173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14618)) 213680173 213712941 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 213680173 213712941).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14618 213680173 213712941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14620)) 213712941 213745709 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 213712941 213745709).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14620 213712941 213745709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14621)) 213745709 213778477 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 213745709 213778477).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14621 213745709 213778477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 213647405 213712941).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 213647405 ≤ 213680173)
    (by decide : 213680173 ≤ 213712941) block0 block1

theorem join_0_1 : (twinPrimeSegment 213712941 213778477).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 213712941 ≤ 213745709)
    (by decide : 213745709 ≤ 213778477) block2 block3

theorem join_1_0 : (twinPrimeSegment 213647405 213778477).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 213647405 ≤ 213712941)
    (by decide : 213712941 ≤ 213778477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 213647405 213778477).card = 445 := join_1_0

end S101C14
end Sude.GeneratedTwinScan
