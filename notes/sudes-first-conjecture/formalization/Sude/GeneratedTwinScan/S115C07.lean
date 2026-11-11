import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15560)) 242090029 242122797 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 242090029 242122797).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15560 242090029 242122797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15561)) 242122797 242155565 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 242122797 242155565).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15561 242122797 242155565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15562)) 242155565 242188333 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 242155565 242188333).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15562 242155565 242188333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15563)) 242188333 242221101 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 242188333 242221101).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15563 242188333 242221101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 242090029 242155565).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 242090029 ≤ 242122797)
    (by decide : 242122797 ≤ 242155565) block0 block1

theorem join_0_1 : (twinPrimeSegment 242155565 242221101).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 242155565 ≤ 242188333)
    (by decide : 242188333 ≤ 242221101) block2 block3

theorem join_1_0 : (twinPrimeSegment 242090029 242221101).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 242090029 ≤ 242155565)
    (by decide : 242155565 ≤ 242221101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 242090029 242221101).card = 443 := join_1_0

end S115C07
end Sude.GeneratedTwinScan
