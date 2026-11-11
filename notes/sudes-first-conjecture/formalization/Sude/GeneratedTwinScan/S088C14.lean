import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13653)) 186384429 186417197 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 186384429 186417197).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13653 186384429 186417197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13654)) 186417197 186449965 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 186417197 186449965).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13654 186417197 186449965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13655)) 186449965 186482733 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 186449965 186482733).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13655 186449965 186482733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13657)) 186482733 186515501 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 186482733 186515501).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13657 186482733 186515501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 186384429 186449965).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 186384429 ≤ 186417197)
    (by decide : 186417197 ≤ 186449965) block0 block1

theorem join_0_1 : (twinPrimeSegment 186449965 186515501).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 186449965 ≤ 186482733)
    (by decide : 186482733 ≤ 186515501) block2 block3

theorem join_1_0 : (twinPrimeSegment 186384429 186515501).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 186384429 ≤ 186449965)
    (by decide : 186449965 ≤ 186515501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 186384429 186515501).card = 478 := join_1_0

end S088C14
end Sude.GeneratedTwinScan
