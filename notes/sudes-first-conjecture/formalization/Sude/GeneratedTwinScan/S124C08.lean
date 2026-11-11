import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16159)) 261095469 261128237 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 261095469 261128237).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16159 261095469 261128237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16160)) 261128237 261161005 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 261128237 261161005).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16160 261128237 261161005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16161)) 261161005 261193773 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 261161005 261193773).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16161 261161005 261193773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16162)) 261193773 261226541 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 261193773 261226541).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16162 261193773 261226541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 261095469 261161005).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 261095469 ≤ 261128237)
    (by decide : 261128237 ≤ 261161005) block0 block1

theorem join_0_1 : (twinPrimeSegment 261161005 261226541).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 261161005 ≤ 261193773)
    (by decide : 261193773 ≤ 261226541) block2 block3

theorem join_1_0 : (twinPrimeSegment 261095469 261226541).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 261095469 ≤ 261161005)
    (by decide : 261161005 ≤ 261226541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 261095469 261226541).card = 479 := join_1_0

end S124C08
end Sude.GeneratedTwinScan
