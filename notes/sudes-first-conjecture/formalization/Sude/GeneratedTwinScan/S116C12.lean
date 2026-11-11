import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15648)) 244842541 244875309 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 244842541 244875309).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15648 244842541 244875309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15649)) 244875309 244908077 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 244875309 244908077).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15649 244875309 244908077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15650)) 244908077 244940845 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 244908077 244940845).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15650 244908077 244940845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15651)) 244940845 244973613 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 244940845 244973613).card = 144 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15651 244940845 244973613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 244842541 244908077).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 244842541 ≤ 244875309)
    (by decide : 244875309 ≤ 244908077) block0 block1

theorem join_0_1 : (twinPrimeSegment 244908077 244973613).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 244908077 ≤ 244940845)
    (by decide : 244940845 ≤ 244973613) block2 block3

theorem join_1_0 : (twinPrimeSegment 244842541 244973613).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 244842541 ≤ 244908077)
    (by decide : 244908077 ≤ 244973613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 244842541 244973613).card = 520 := join_1_0

end S116C12
end Sude.GeneratedTwinScan
