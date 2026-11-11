import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17085)) 291897389 291930157 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 291897389 291930157).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17085 291897389 291930157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17086)) 291930157 291962925 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 291930157 291962925).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17086 291930157 291962925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17087)) 291962925 291995693 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 291962925 291995693).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17087 291962925 291995693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17088)) 291995693 292028461 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 291995693 292028461).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17088 291995693 292028461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 291897389 291962925).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 291897389 ≤ 291930157)
    (by decide : 291930157 ≤ 291962925) block0 block1

theorem join_0_1 : (twinPrimeSegment 291962925 292028461).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 291962925 ≤ 291995693)
    (by decide : 291995693 ≤ 292028461) block2 block3

theorem join_1_0 : (twinPrimeSegment 291897389 292028461).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 291897389 ≤ 291962925)
    (by decide : 291962925 ≤ 292028461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 291897389 292028461).card = 457 := join_1_0

end S139C03
end Sude.GeneratedTwinScan
