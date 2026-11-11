import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12448)) 154927149 154959917 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 154927149 154959917).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12448 154927149 154959917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12449)) 154959917 154992685 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 154959917 154992685).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12449 154959917 154992685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12450)) 154992685 155025453 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 154992685 155025453).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12450 154992685 155025453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12452)) 155025453 155058221 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 155025453 155058221).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12452 155025453 155058221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 154927149 154992685).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 154927149 ≤ 154959917)
    (by decide : 154959917 ≤ 154992685) block0 block1

theorem join_0_1 : (twinPrimeSegment 154992685 155058221).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 154992685 ≤ 155025453)
    (by decide : 155025453 ≤ 155058221) block2 block3

theorem join_1_0 : (twinPrimeSegment 154927149 155058221).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 154927149 ≤ 154992685)
    (by decide : 154992685 ≤ 155058221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 154927149 155058221).card = 487 := join_1_0

end S073C14
end Sude.GeneratedTwinScan
