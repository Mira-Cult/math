import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20703)) 428605485 428638253 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 428605485 428638253).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20703 428605485 428638253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20704)) 428638253 428671021 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 428638253 428671021).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20704 428638253 428671021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20705)) 428671021 428703789 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 428671021 428703789).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20705 428671021 428703789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20705)) 428703789 428736557 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 428703789 428736557).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20705 428703789 428736557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 428605485 428671021).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 428605485 ≤ 428638253)
    (by decide : 428638253 ≤ 428671021) block0 block1

theorem join_0_1 : (twinPrimeSegment 428671021 428736557).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 428671021 ≤ 428703789)
    (by decide : 428703789 ≤ 428736557) block2 block3

theorem join_1_0 : (twinPrimeSegment 428605485 428736557).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 428605485 ≤ 428671021)
    (by decide : 428671021 ≤ 428736557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 428605485 428736557).card = 453 := join_1_0

end S204C06
end Sude.GeneratedTwinScan
