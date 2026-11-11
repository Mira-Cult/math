import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21989)) 483524653 483557421 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 483524653 483557421).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21989 483524653 483557421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21990)) 483557421 483590189 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 483557421 483590189).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21990 483557421 483590189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21991)) 483590189 483622957 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 483590189 483622957).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21991 483590189 483622957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21992)) 483622957 483655725 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 483622957 483655725).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21992 483622957 483655725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 483524653 483590189).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 483524653 ≤ 483557421)
    (by decide : 483557421 ≤ 483590189) block0 block1

theorem join_0_1 : (twinPrimeSegment 483590189 483655725).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 483590189 ≤ 483622957)
    (by decide : 483622957 ≤ 483655725) block2 block3

theorem join_1_0 : (twinPrimeSegment 483524653 483655725).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 483524653 ≤ 483590189)
    (by decide : 483590189 ≤ 483655725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 483524653 483655725).card = 434 := join_1_0

end S230C09
end Sude.GeneratedTwinScan
