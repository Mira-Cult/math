import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21759)) 473432109 473464877 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 473432109 473464877).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21759 473432109 473464877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21760)) 473464877 473497645 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 473464877 473497645).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21760 473464877 473497645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21760)) 473497645 473530413 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 473497645 473530413).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21760 473497645 473530413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21761)) 473530413 473563181 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 473530413 473563181).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21761 473530413 473563181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 473432109 473497645).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 473432109 ≤ 473464877)
    (by decide : 473464877 ≤ 473497645) block0 block1

theorem join_0_1 : (twinPrimeSegment 473497645 473563181).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 473497645 ≤ 473530413)
    (by decide : 473530413 ≤ 473563181) block2 block3

theorem join_1_0 : (twinPrimeSegment 473432109 473563181).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 473432109 ≤ 473497645)
    (by decide : 473497645 ≤ 473563181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 473432109 473563181).card = 437 := join_1_0

end S225C12
end Sude.GeneratedTwinScan
