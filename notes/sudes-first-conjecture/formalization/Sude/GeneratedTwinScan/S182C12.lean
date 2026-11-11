import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19577)) 383254573 383287341 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 383254573 383287341).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19577 383254573 383287341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19578)) 383287341 383320109 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 383287341 383320109).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19578 383287341 383320109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19579)) 383320109 383352877 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 383320109 383352877).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19579 383320109 383352877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19580)) 383352877 383385645 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 383352877 383385645).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19580 383352877 383385645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 383254573 383320109).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 383254573 ≤ 383287341)
    (by decide : 383287341 ≤ 383320109) block0 block1

theorem join_0_1 : (twinPrimeSegment 383320109 383385645).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 383320109 ≤ 383352877)
    (by decide : 383352877 ≤ 383385645) block2 block3

theorem join_1_0 : (twinPrimeSegment 383254573 383385645).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 383254573 ≤ 383320109)
    (by decide : 383320109 ≤ 383385645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 383254573 383385645).card = 443 := join_1_0

end S182C12
end Sude.GeneratedTwinScan
