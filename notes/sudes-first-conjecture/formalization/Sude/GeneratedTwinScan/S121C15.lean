import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15992)) 255721517 255754285 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 255721517 255754285).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15992 255721517 255754285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15993)) 255754285 255787053 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 255754285 255787053).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15993 255754285 255787053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15994)) 255787053 255819821 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 255787053 255819821).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15994 255787053 255819821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15995)) 255819821 255852589 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 255819821 255852589).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15995 255819821 255852589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 255721517 255787053).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 255721517 ≤ 255754285)
    (by decide : 255754285 ≤ 255787053) block0 block1

theorem join_0_1 : (twinPrimeSegment 255787053 255852589).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 255787053 ≤ 255819821)
    (by decide : 255819821 ≤ 255852589) block2 block3

theorem join_1_0 : (twinPrimeSegment 255721517 255852589).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 255721517 ≤ 255787053)
    (by decide : 255787053 ≤ 255852589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 255721517 255852589).card = 473 := join_1_0

end S121C15
end Sude.GeneratedTwinScan
