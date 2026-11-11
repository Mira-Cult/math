import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18722)) 350486573 350519341 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 350486573 350519341).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18722 350486573 350519341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18723)) 350519341 350552109 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 350519341 350552109).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18723 350519341 350552109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18723)) 350552109 350584877 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 350552109 350584877).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18723 350552109 350584877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18724)) 350584877 350617645 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 350584877 350617645).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18724 350584877 350617645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 350486573 350552109).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 350486573 ≤ 350519341)
    (by decide : 350519341 ≤ 350552109) block0 block1

theorem join_0_1 : (twinPrimeSegment 350552109 350617645).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 350552109 ≤ 350584877)
    (by decide : 350584877 ≤ 350617645) block2 block3

theorem join_1_0 : (twinPrimeSegment 350486573 350617645).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 350486573 ≤ 350552109)
    (by decide : 350552109 ≤ 350617645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 350486573 350617645).card = 452 := join_1_0

end S167C02
end Sude.GeneratedTwinScan
