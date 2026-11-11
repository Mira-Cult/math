import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21400)) 457965613 457998381 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 457965613 457998381).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21400 457965613 457998381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21401)) 457998381 458031149 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 457998381 458031149).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21401 457998381 458031149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21402)) 458031149 458063917 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 458031149 458063917).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21402 458031149 458063917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21403)) 458063917 458096685 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 458063917 458096685).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21403 458063917 458096685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 457965613 458031149).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 457965613 ≤ 457998381)
    (by decide : 457998381 ≤ 458031149) block0 block1

theorem join_0_1 : (twinPrimeSegment 458031149 458096685).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 458031149 ≤ 458063917)
    (by decide : 458063917 ≤ 458096685) block2 block3

theorem join_1_0 : (twinPrimeSegment 457965613 458096685).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 457965613 ≤ 458031149)
    (by decide : 458031149 ≤ 458096685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 457965613 458096685).card = 459 := join_1_0

end S218C06
end Sude.GeneratedTwinScan
