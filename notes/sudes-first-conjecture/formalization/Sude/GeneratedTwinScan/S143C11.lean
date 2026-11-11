import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17359)) 301334573 301367341 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 301334573 301367341).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17359 301334573 301367341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17360)) 301367341 301400109 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 301367341 301400109).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17360 301367341 301400109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17361)) 301400109 301432877 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 301400109 301432877).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17361 301400109 301432877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17362)) 301432877 301465645 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 301432877 301465645).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17362 301432877 301465645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 301334573 301400109).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 301334573 ≤ 301367341)
    (by decide : 301367341 ≤ 301400109) block0 block1

theorem join_0_1 : (twinPrimeSegment 301400109 301465645).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 301400109 ≤ 301432877)
    (by decide : 301432877 ≤ 301465645) block2 block3

theorem join_1_0 : (twinPrimeSegment 301334573 301465645).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 301334573 ≤ 301400109)
    (by decide : 301400109 ≤ 301465645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 301334573 301465645).card = 472 := join_1_0

end S143C11
end Sude.GeneratedTwinScan
