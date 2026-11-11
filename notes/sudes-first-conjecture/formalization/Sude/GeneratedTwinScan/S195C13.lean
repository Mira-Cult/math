import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20265)) 410648621 410681389 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 410648621 410681389).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20265 410648621 410681389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20266)) 410681389 410714157 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 410681389 410714157).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20266 410681389 410714157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20266)) 410714157 410746925 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 410714157 410746925).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20266 410714157 410746925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20267)) 410746925 410779693 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 410746925 410779693).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20267 410746925 410779693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 410648621 410714157).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 410648621 ≤ 410681389)
    (by decide : 410681389 ≤ 410714157) block0 block1

theorem join_0_1 : (twinPrimeSegment 410714157 410779693).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 410714157 ≤ 410746925)
    (by decide : 410746925 ≤ 410779693) block2 block3

theorem join_1_0 : (twinPrimeSegment 410648621 410779693).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 410648621 ≤ 410714157)
    (by decide : 410714157 ≤ 410779693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 410648621 410779693).card = 441 := join_1_0

end S195C13
end Sude.GeneratedTwinScan
