import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19744)) 389808173 389840941 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 389808173 389840941).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19744 389808173 389840941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19745)) 389840941 389873709 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 389840941 389873709).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19745 389840941 389873709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19746)) 389873709 389906477 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 389873709 389906477).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19746 389873709 389906477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19746)) 389906477 389939245 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 389906477 389939245).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19746 389906477 389939245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 389808173 389873709).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 389808173 ≤ 389840941)
    (by decide : 389840941 ≤ 389873709) block0 block1

theorem join_0_1 : (twinPrimeSegment 389873709 389939245).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 389873709 ≤ 389906477)
    (by decide : 389906477 ≤ 389939245) block2 block3

theorem join_1_0 : (twinPrimeSegment 389808173 389939245).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 389808173 ≤ 389873709)
    (by decide : 389873709 ≤ 389939245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 389808173 389939245).card = 447 := join_1_0

end S185C14
end Sude.GeneratedTwinScan
