import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17924)) 321257517 321290285 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 321257517 321290285).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17924 321257517 321290285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17925)) 321290285 321323053 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 321290285 321323053).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17925 321290285 321323053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17926)) 321323053 321355821 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 321323053 321355821).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17926 321323053 321355821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17927)) 321355821 321388589 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 321355821 321388589).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17927 321355821 321388589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 321257517 321323053).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 321257517 ≤ 321290285)
    (by decide : 321290285 ≤ 321323053) block0 block1

theorem join_0_1 : (twinPrimeSegment 321323053 321388589).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 321323053 ≤ 321355821)
    (by decide : 321355821 ≤ 321388589) block2 block3

theorem join_1_0 : (twinPrimeSegment 321257517 321388589).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 321257517 ≤ 321323053)
    (by decide : 321323053 ≤ 321388589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 321257517 321388589).card = 442 := join_1_0

end S153C03
end Sude.GeneratedTwinScan
