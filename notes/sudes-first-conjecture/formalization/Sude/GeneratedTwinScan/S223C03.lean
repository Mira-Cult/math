import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21635)) 468058157 468090925 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 468058157 468090925).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21635 468058157 468090925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21636)) 468090925 468123693 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 468090925 468123693).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21636 468090925 468123693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21636)) 468123693 468156461 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 468123693 468156461).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21636 468123693 468156461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21637)) 468156461 468189229 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 468156461 468189229).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21637 468156461 468189229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 468058157 468123693).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 468058157 ≤ 468090925)
    (by decide : 468090925 ≤ 468123693) block0 block1

theorem join_0_1 : (twinPrimeSegment 468123693 468189229).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 468123693 ≤ 468156461)
    (by decide : 468156461 ≤ 468189229) block2 block3

theorem join_1_0 : (twinPrimeSegment 468058157 468189229).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 468058157 ≤ 468123693)
    (by decide : 468123693 ≤ 468189229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 468058157 468189229).card = 443 := join_1_0

end S223C03
end Sude.GeneratedTwinScan
