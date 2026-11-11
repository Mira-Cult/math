import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22757)) 517865517 517898285 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 517865517 517898285).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22757 517865517 517898285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22758)) 517898285 517931053 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 517898285 517931053).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22758 517898285 517931053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22758)) 517931053 517963821 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 517931053 517963821).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22758 517931053 517963821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22759)) 517963821 517996589 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 517963821 517996589).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22759 517963821 517996589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 517865517 517931053).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 517865517 ≤ 517898285)
    (by decide : 517898285 ≤ 517931053) block0 block1

theorem join_0_1 : (twinPrimeSegment 517931053 517996589).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 517931053 ≤ 517963821)
    (by decide : 517963821 ≤ 517996589) block2 block3

theorem join_1_0 : (twinPrimeSegment 517865517 517996589).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 517865517 ≤ 517931053)
    (by decide : 517931053 ≤ 517996589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 517865517 517996589).card = 446 := join_1_0

end S246C15
end Sude.GeneratedTwinScan
