import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16966)) 287834157 287866925 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 287834157 287866925).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16966 287834157 287866925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16967)) 287866925 287899693 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 287866925 287899693).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16967 287866925 287899693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16968)) 287899693 287932461 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 287899693 287932461).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16968 287899693 287932461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16969)) 287932461 287965229 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 287932461 287965229).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16969 287932461 287965229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 287834157 287899693).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 287834157 ≤ 287866925)
    (by decide : 287866925 ≤ 287899693) block0 block1

theorem join_0_1 : (twinPrimeSegment 287899693 287965229).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 287899693 ≤ 287932461)
    (by decide : 287932461 ≤ 287965229) block2 block3

theorem join_1_0 : (twinPrimeSegment 287834157 287965229).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 287834157 ≤ 287899693)
    (by decide : 287899693 ≤ 287965229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 287834157 287965229).card = 458 := join_1_0

end S137C04
end Sude.GeneratedTwinScan
