import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18673)) 348651565 348684333 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 348651565 348684333).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18673 348651565 348684333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18673)) 348684333 348717101 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 348684333 348717101).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18673 348684333 348717101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18674)) 348717101 348749869 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 348717101 348749869).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18674 348717101 348749869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18675)) 348749869 348782637 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 348749869 348782637).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18675 348749869 348782637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 348651565 348717101).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 348651565 ≤ 348684333)
    (by decide : 348684333 ≤ 348717101) block0 block1

theorem join_0_1 : (twinPrimeSegment 348717101 348782637).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 348717101 ≤ 348749869)
    (by decide : 348749869 ≤ 348782637) block2 block3

theorem join_1_0 : (twinPrimeSegment 348651565 348782637).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 348651565 ≤ 348717101)
    (by decide : 348717101 ≤ 348782637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 348651565 348782637).card = 449 := join_1_0

end S166C04
end Sude.GeneratedTwinScan
