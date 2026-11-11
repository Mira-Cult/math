import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16208)) 262668333 262701101 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 262668333 262701101).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16208 262668333 262701101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16209)) 262701101 262733869 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 262701101 262733869).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16209 262701101 262733869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16210)) 262733869 262766637 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 262733869 262766637).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16210 262733869 262766637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16211)) 262766637 262799405 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 262766637 262799405).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16211 262766637 262799405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 262668333 262733869).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 262668333 ≤ 262701101)
    (by decide : 262701101 ≤ 262733869) block0 block1

theorem join_0_1 : (twinPrimeSegment 262733869 262799405).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 262733869 ≤ 262766637)
    (by decide : 262766637 ≤ 262799405) block2 block3

theorem join_1_0 : (twinPrimeSegment 262668333 262799405).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 262668333 ≤ 262733869)
    (by decide : 262733869 ≤ 262799405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 262668333 262799405).card = 439 := join_1_0

end S125C04
end Sude.GeneratedTwinScan
