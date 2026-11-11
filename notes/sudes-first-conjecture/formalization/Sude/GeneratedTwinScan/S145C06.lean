import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17461)) 304873517 304906285 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 304873517 304906285).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17461 304873517 304906285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17462)) 304906285 304939053 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 304906285 304939053).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17462 304906285 304939053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17463)) 304939053 304971821 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 304939053 304971821).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17463 304939053 304971821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17464)) 304971821 305004589 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 304971821 305004589).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17464 304971821 305004589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 304873517 304939053).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 304873517 ≤ 304906285)
    (by decide : 304906285 ≤ 304939053) block0 block1

theorem join_0_1 : (twinPrimeSegment 304939053 305004589).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 304939053 ≤ 304971821)
    (by decide : 304971821 ≤ 305004589) block2 block3

theorem join_1_0 : (twinPrimeSegment 304873517 305004589).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 304873517 ≤ 304939053)
    (by decide : 304939053 ≤ 305004589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 304873517 305004589).card = 494 := join_1_0

end S145C06
end Sude.GeneratedTwinScan
