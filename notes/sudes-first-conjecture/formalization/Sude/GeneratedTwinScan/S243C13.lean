import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22612)) 511311917 511344685 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 511311917 511344685).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22612 511311917 511344685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22613)) 511344685 511377453 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 511344685 511377453).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22613 511344685 511377453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22614)) 511377453 511410221 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 511377453 511410221).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22614 511377453 511410221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22615)) 511410221 511442989 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 511410221 511442989).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22615 511410221 511442989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 511311917 511377453).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 511311917 ≤ 511344685)
    (by decide : 511344685 ≤ 511377453) block0 block1

theorem join_0_1 : (twinPrimeSegment 511377453 511442989).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 511377453 ≤ 511410221)
    (by decide : 511410221 ≤ 511442989) block2 block3

theorem join_1_0 : (twinPrimeSegment 511311917 511442989).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 511311917 ≤ 511377453)
    (by decide : 511377453 ≤ 511442989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 511311917 511442989).card = 434 := join_1_0

end S243C13
end Sude.GeneratedTwinScan
