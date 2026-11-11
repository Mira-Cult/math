import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21732)) 472252461 472285229 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 472252461 472285229).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21732 472252461 472285229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21732)) 472285229 472317997 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 472285229 472317997).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21732 472285229 472317997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21733)) 472317997 472350765 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 472317997 472350765).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21733 472317997 472350765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21734)) 472350765 472383533 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 472350765 472383533).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21734 472350765 472383533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 472252461 472317997).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 472252461 ≤ 472285229)
    (by decide : 472285229 ≤ 472317997) block0 block1

theorem join_0_1 : (twinPrimeSegment 472317997 472383533).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 472317997 ≤ 472350765)
    (by decide : 472350765 ≤ 472383533) block2 block3

theorem join_1_0 : (twinPrimeSegment 472252461 472383533).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 472252461 ≤ 472317997)
    (by decide : 472317997 ≤ 472383533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 472252461 472383533).card = 431 := join_1_0

end S225C03
end Sude.GeneratedTwinScan
