import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21774)) 474087469 474120237 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 474087469 474120237).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21774 474087469 474120237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21775)) 474120237 474153005 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 474120237 474153005).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21775 474120237 474153005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21775)) 474153005 474185773 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 474153005 474185773).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21775 474153005 474185773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21776)) 474185773 474218541 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 474185773 474218541).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21776 474185773 474218541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 474087469 474153005).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 474087469 ≤ 474120237)
    (by decide : 474120237 ≤ 474153005) block0 block1

theorem join_0_1 : (twinPrimeSegment 474153005 474218541).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 474153005 ≤ 474185773)
    (by decide : 474185773 ≤ 474218541) block2 block3

theorem join_1_0 : (twinPrimeSegment 474087469 474218541).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 474087469 ≤ 474153005)
    (by decide : 474153005 ≤ 474218541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 474087469 474218541).card = 425 := join_1_0

end S226C01
end Sude.GeneratedTwinScan
