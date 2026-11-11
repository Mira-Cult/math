import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18196)) 331087917 331120685 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 331087917 331120685).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18196 331087917 331120685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18197)) 331120685 331153453 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 331120685 331153453).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18197 331120685 331153453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18198)) 331153453 331186221 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 331153453 331186221).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18198 331153453 331186221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18199)) 331186221 331218989 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 331186221 331218989).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18199 331186221 331218989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 331087917 331153453).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 331087917 ≤ 331120685)
    (by decide : 331120685 ≤ 331153453) block0 block1

theorem join_0_1 : (twinPrimeSegment 331153453 331218989).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 331153453 ≤ 331186221)
    (by decide : 331186221 ≤ 331218989) block2 block3

theorem join_1_0 : (twinPrimeSegment 331087917 331218989).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 331087917 ≤ 331153453)
    (by decide : 331153453 ≤ 331218989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 331087917 331218989).card = 440 := join_1_0

end S157C14
end Sude.GeneratedTwinScan
