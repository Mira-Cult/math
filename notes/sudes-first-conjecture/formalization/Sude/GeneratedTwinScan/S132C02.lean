import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16646)) 277086253 277119021 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 277086253 277119021).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16646 277086253 277119021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16647)) 277119021 277151789 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 277119021 277151789).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16647 277119021 277151789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16648)) 277151789 277184557 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 277151789 277184557).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16648 277151789 277184557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16649)) 277184557 277217325 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 277184557 277217325).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16649 277184557 277217325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 277086253 277151789).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 277086253 ≤ 277119021)
    (by decide : 277119021 ≤ 277151789) block0 block1

theorem join_0_1 : (twinPrimeSegment 277151789 277217325).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 277151789 ≤ 277184557)
    (by decide : 277184557 ≤ 277217325) block2 block3

theorem join_1_0 : (twinPrimeSegment 277086253 277217325).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 277086253 ≤ 277151789)
    (by decide : 277151789 ≤ 277217325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 277086253 277217325).card = 437 := join_1_0

end S132C02
end Sude.GeneratedTwinScan
