import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13523)) 182845485 182878253 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 182845485 182878253).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13523 182845485 182878253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13524)) 182878253 182911021 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 182878253 182911021).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13524 182878253 182911021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13525)) 182911021 182943789 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 182911021 182943789).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13525 182911021 182943789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13526)) 182943789 182976557 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 182943789 182976557).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13526 182943789 182976557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 182845485 182911021).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 182845485 ≤ 182878253)
    (by decide : 182878253 ≤ 182911021) block0 block1

theorem join_0_1 : (twinPrimeSegment 182911021 182976557).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 182911021 ≤ 182943789)
    (by decide : 182943789 ≤ 182976557) block2 block3

theorem join_1_0 : (twinPrimeSegment 182845485 182976557).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 182845485 ≤ 182911021)
    (by decide : 182911021 ≤ 182976557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 182845485 182976557).card = 476 := join_1_0

end S087C03
end Sude.GeneratedTwinScan
