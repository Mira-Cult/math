import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18715)) 350224429 350257197 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 350224429 350257197).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18715 350224429 350257197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18716)) 350257197 350289965 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 350257197 350289965).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18716 350257197 350289965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18716)) 350289965 350322733 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 350289965 350322733).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18716 350289965 350322733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18717)) 350322733 350355501 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 350322733 350355501).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18717 350322733 350355501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 350224429 350289965).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 350224429 ≤ 350257197)
    (by decide : 350257197 ≤ 350289965) block0 block1

theorem join_0_1 : (twinPrimeSegment 350289965 350355501).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 350289965 ≤ 350322733)
    (by decide : 350322733 ≤ 350355501) block2 block3

theorem join_1_0 : (twinPrimeSegment 350224429 350355501).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 350224429 ≤ 350289965)
    (by decide : 350289965 ≤ 350355501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 350224429 350355501).card = 432 := join_1_0

end S167C00
end Sude.GeneratedTwinScan
