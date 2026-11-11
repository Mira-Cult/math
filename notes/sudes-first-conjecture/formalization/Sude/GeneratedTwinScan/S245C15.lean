import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22711)) 515768365 515801133 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 515768365 515801133).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22711 515768365 515801133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22711)) 515801133 515833901 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 515801133 515833901).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22711 515801133 515833901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22712)) 515833901 515866669 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 515833901 515866669).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22712 515833901 515866669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22713)) 515866669 515899437 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 515866669 515899437).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22713 515866669 515899437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 515768365 515833901).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 515768365 ≤ 515801133)
    (by decide : 515801133 ≤ 515833901) block0 block1

theorem join_0_1 : (twinPrimeSegment 515833901 515899437).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 515833901 ≤ 515866669)
    (by decide : 515866669 ≤ 515899437) block2 block3

theorem join_1_0 : (twinPrimeSegment 515768365 515899437).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 515768365 ≤ 515833901)
    (by decide : 515833901 ≤ 515899437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 515768365 515899437).card = 470 := join_1_0

end S245C15
end Sude.GeneratedTwinScan
