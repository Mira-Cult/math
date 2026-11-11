import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21179)) 448528429 448561197 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 448528429 448561197).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21179 448528429 448561197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21180)) 448561197 448593965 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 448561197 448593965).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21180 448561197 448593965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21180)) 448593965 448626733 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 448593965 448626733).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21180 448593965 448626733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21181)) 448626733 448659501 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 448626733 448659501).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21181 448626733 448659501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 448528429 448593965).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 448528429 ≤ 448561197)
    (by decide : 448561197 ≤ 448593965) block0 block1

theorem join_0_1 : (twinPrimeSegment 448593965 448659501).card = 193 := by
  simpa using combineTwinPrimeSegments (by decide : 448593965 ≤ 448626733)
    (by decide : 448626733 ≤ 448659501) block2 block3

theorem join_1_0 : (twinPrimeSegment 448528429 448659501).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 448528429 ≤ 448593965)
    (by decide : 448593965 ≤ 448659501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 448528429 448659501).card = 432 := join_1_0

end S213C14
end Sude.GeneratedTwinScan
