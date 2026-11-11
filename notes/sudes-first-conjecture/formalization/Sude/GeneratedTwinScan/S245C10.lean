import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22696)) 515113005 515145773 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 515113005 515145773).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22696 515113005 515145773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22697)) 515145773 515178541 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 515145773 515178541).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22697 515145773 515178541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22698)) 515178541 515211309 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 515178541 515211309).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22698 515178541 515211309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22698)) 515211309 515244077 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 515211309 515244077).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22698 515211309 515244077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 515113005 515178541).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 515113005 ≤ 515145773)
    (by decide : 515145773 ≤ 515178541) block0 block1

theorem join_0_1 : (twinPrimeSegment 515178541 515244077).card = 188 := by
  simpa using combineTwinPrimeSegments (by decide : 515178541 ≤ 515211309)
    (by decide : 515211309 ≤ 515244077) block2 block3

theorem join_1_0 : (twinPrimeSegment 515113005 515244077).card = 397 := by
  simpa using combineTwinPrimeSegments (by decide : 515113005 ≤ 515178541)
    (by decide : 515178541 ≤ 515244077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 515113005 515244077).card = 397 := join_1_0

end S245C10
end Sude.GeneratedTwinScan
