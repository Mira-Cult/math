import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22253)) 495190061 495222829 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 495190061 495222829).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22253 495190061 495222829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22254)) 495222829 495255597 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 495222829 495255597).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22254 495222829 495255597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22255)) 495255597 495288365 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 495255597 495288365).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22255 495255597 495288365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22255)) 495288365 495321133 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 495288365 495321133).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22255 495288365 495321133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 495190061 495255597).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 495190061 ≤ 495222829)
    (by decide : 495222829 ≤ 495255597) block0 block1

theorem join_0_1 : (twinPrimeSegment 495255597 495321133).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 495255597 ≤ 495288365)
    (by decide : 495288365 ≤ 495321133) block2 block3

theorem join_1_0 : (twinPrimeSegment 495190061 495321133).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 495190061 ≤ 495255597)
    (by decide : 495255597 ≤ 495321133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 495190061 495321133).card = 443 := join_1_0

end S236C02
end Sude.GeneratedTwinScan
