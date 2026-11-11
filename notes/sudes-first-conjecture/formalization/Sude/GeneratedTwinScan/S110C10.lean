import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15232)) 231997485 232030253 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 231997485 232030253).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15232 231997485 232030253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15233)) 232030253 232063021 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 232030253 232063021).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15233 232030253 232063021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15234)) 232063021 232095789 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 232063021 232095789).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15234 232063021 232095789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15235)) 232095789 232128557 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 232095789 232128557).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15235 232095789 232128557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 231997485 232063021).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 231997485 ≤ 232030253)
    (by decide : 232030253 ≤ 232063021) block0 block1

theorem join_0_1 : (twinPrimeSegment 232063021 232128557).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 232063021 ≤ 232095789)
    (by decide : 232095789 ≤ 232128557) block2 block3

theorem join_1_0 : (twinPrimeSegment 231997485 232128557).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 231997485 ≤ 232063021)
    (by decide : 232063021 ≤ 232128557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 231997485 232128557).card = 450 := join_1_0

end S110C10
end Sude.GeneratedTwinScan
