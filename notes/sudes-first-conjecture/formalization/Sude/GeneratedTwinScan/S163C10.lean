import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18525)) 343146541 343179309 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 343146541 343179309).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18525 343146541 343179309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18525)) 343179309 343212077 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 343179309 343212077).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18525 343179309 343212077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18526)) 343212077 343244845 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 343212077 343244845).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18526 343212077 343244845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18527)) 343244845 343277613 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 343244845 343277613).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18527 343244845 343277613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 343146541 343212077).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 343146541 ≤ 343179309)
    (by decide : 343179309 ≤ 343212077) block0 block1

theorem join_0_1 : (twinPrimeSegment 343212077 343277613).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 343212077 ≤ 343244845)
    (by decide : 343244845 ≤ 343277613) block2 block3

theorem join_1_0 : (twinPrimeSegment 343146541 343277613).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 343146541 ≤ 343212077)
    (by decide : 343212077 ≤ 343277613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 343146541 343277613).card = 459 := join_1_0

end S163C10
end Sude.GeneratedTwinScan
