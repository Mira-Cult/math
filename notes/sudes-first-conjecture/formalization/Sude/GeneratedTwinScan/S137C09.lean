import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16985)) 288489517 288522285 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 288489517 288522285).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16985 288489517 288522285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16986)) 288522285 288555053 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 288522285 288555053).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16986 288522285 288555053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16987)) 288555053 288587821 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 288555053 288587821).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16987 288555053 288587821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16988)) 288587821 288620589 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 288587821 288620589).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16988 288587821 288620589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 288489517 288555053).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 288489517 ≤ 288522285)
    (by decide : 288522285 ≤ 288555053) block0 block1

theorem join_0_1 : (twinPrimeSegment 288555053 288620589).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 288555053 ≤ 288587821)
    (by decide : 288587821 ≤ 288620589) block2 block3

theorem join_1_0 : (twinPrimeSegment 288489517 288620589).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 288489517 ≤ 288555053)
    (by decide : 288555053 ≤ 288620589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 288489517 288620589).card = 453 := join_1_0

end S137C09
end Sude.GeneratedTwinScan
