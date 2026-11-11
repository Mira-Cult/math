import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21650)) 468713517 468746285 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 468713517 468746285).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21650 468713517 468746285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21651)) 468746285 468779053 = 91 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 468746285 468779053).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21651 468746285 468779053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21652)) 468779053 468811821 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 468779053 468811821).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21652 468779053 468811821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21652)) 468811821 468844589 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 468811821 468844589).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21652 468811821 468844589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 468713517 468779053).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 468713517 ≤ 468746285)
    (by decide : 468746285 ≤ 468779053) block0 block1

theorem join_0_1 : (twinPrimeSegment 468779053 468844589).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 468779053 ≤ 468811821)
    (by decide : 468811821 ≤ 468844589) block2 block3

theorem join_1_0 : (twinPrimeSegment 468713517 468844589).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 468713517 ≤ 468779053)
    (by decide : 468779053 ≤ 468844589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 468713517 468844589).card = 420 := join_1_0

end S223C08
end Sude.GeneratedTwinScan
