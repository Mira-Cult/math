import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S197C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20336)) 413532205 413564973 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 413532205 413564973).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20336 413532205 413564973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20337)) 413564973 413597741 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 413564973 413597741).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20337 413564973 413597741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20337)) 413597741 413630509 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 413597741 413630509).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20337 413597741 413630509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20338)) 413630509 413663277 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 413630509 413663277).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20338 413630509 413663277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 413532205 413597741).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 413532205 ≤ 413564973)
    (by decide : 413564973 ≤ 413597741) block0 block1

theorem join_0_1 : (twinPrimeSegment 413597741 413663277).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 413597741 ≤ 413630509)
    (by decide : 413630509 ≤ 413663277) block2 block3

theorem join_1_0 : (twinPrimeSegment 413532205 413663277).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 413532205 ≤ 413597741)
    (by decide : 413597741 ≤ 413663277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 413532205 413663277).card = 439 := join_1_0

end S197C03
end Sude.GeneratedTwinScan
