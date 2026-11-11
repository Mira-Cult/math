import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13518)) 182714413 182747181 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 182714413 182747181).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13518 182714413 182747181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13519)) 182747181 182779949 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 182747181 182779949).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13519 182747181 182779949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13520)) 182779949 182812717 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 182779949 182812717).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13520 182779949 182812717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13522)) 182812717 182845485 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 182812717 182845485).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13522 182812717 182845485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 182714413 182779949).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 182714413 ≤ 182747181)
    (by decide : 182747181 ≤ 182779949) block0 block1

theorem join_0_1 : (twinPrimeSegment 182779949 182845485).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 182779949 ≤ 182812717)
    (by decide : 182812717 ≤ 182845485) block2 block3

theorem join_1_0 : (twinPrimeSegment 182714413 182845485).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 182714413 ≤ 182779949)
    (by decide : 182779949 ≤ 182845485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 182714413 182845485).card = 450 := join_1_0

end S087C02
end Sude.GeneratedTwinScan
