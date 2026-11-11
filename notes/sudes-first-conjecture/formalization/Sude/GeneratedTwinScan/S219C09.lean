import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21459)) 460455981 460488749 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 460455981 460488749).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21459 460455981 460488749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21459)) 460488749 460521517 = 91 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 460488749 460521517).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21459 460488749 460521517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21460)) 460521517 460554285 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 460521517 460554285).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21460 460521517 460554285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21461)) 460554285 460587053 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 460554285 460587053).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21461 460554285 460587053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 460455981 460521517).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 460455981 ≤ 460488749)
    (by decide : 460488749 ≤ 460521517) block0 block1

theorem join_0_1 : (twinPrimeSegment 460521517 460587053).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 460521517 ≤ 460554285)
    (by decide : 460554285 ≤ 460587053) block2 block3

theorem join_1_0 : (twinPrimeSegment 460455981 460587053).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 460455981 ≤ 460521517)
    (by decide : 460521517 ≤ 460587053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 460455981 460587053).card = 419 := join_1_0

end S219C09
end Sude.GeneratedTwinScan
