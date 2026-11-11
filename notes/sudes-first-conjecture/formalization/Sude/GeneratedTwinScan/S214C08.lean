import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21210)) 449839149 449871917 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 449839149 449871917).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21210 449839149 449871917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21210)) 449871917 449904685 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 449871917 449904685).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21210 449871917 449904685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21211)) 449904685 449937453 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 449904685 449937453).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21211 449904685 449937453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21212)) 449937453 449970221 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 449937453 449970221).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21212 449937453 449970221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 449839149 449904685).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 449839149 ≤ 449871917)
    (by decide : 449871917 ≤ 449904685) block0 block1

theorem join_0_1 : (twinPrimeSegment 449904685 449970221).card = 190 := by
  simpa using combineTwinPrimeSegments (by decide : 449904685 ≤ 449937453)
    (by decide : 449937453 ≤ 449970221) block2 block3

theorem join_1_0 : (twinPrimeSegment 449839149 449970221).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 449839149 ≤ 449904685)
    (by decide : 449904685 ≤ 449970221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 449839149 449970221).card = 416 := join_1_0

end S214C08
end Sude.GeneratedTwinScan
