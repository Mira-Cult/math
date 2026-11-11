import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18375)) 337641517 337674285 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 337641517 337674285).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18375 337641517 337674285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18376)) 337674285 337707053 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 337674285 337707053).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18376 337674285 337707053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18377)) 337707053 337739821 = 90 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 337707053 337739821).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18377 337707053 337739821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18378)) 337739821 337772589 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 337739821 337772589).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18378 337739821 337772589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 337641517 337707053).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 337641517 ≤ 337674285)
    (by decide : 337674285 ≤ 337707053) block0 block1

theorem join_0_1 : (twinPrimeSegment 337707053 337772589).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 337707053 ≤ 337739821)
    (by decide : 337739821 ≤ 337772589) block2 block3

theorem join_1_0 : (twinPrimeSegment 337641517 337772589).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 337641517 ≤ 337707053)
    (by decide : 337707053 ≤ 337772589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 337641517 337772589).card = 423 := join_1_0

end S161C00
end Sude.GeneratedTwinScan
