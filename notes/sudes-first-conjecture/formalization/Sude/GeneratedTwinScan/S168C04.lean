import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18785)) 352845869 352878637 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 352845869 352878637).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18785 352845869 352878637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18785)) 352878637 352911405 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 352878637 352911405).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18785 352878637 352911405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18786)) 352911405 352944173 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 352911405 352944173).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18786 352911405 352944173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18787)) 352944173 352976941 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 352944173 352976941).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18787 352944173 352976941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 352845869 352911405).card = 193 := by
  simpa using combineTwinPrimeSegments (by decide : 352845869 ≤ 352878637)
    (by decide : 352878637 ≤ 352911405) block0 block1

theorem join_0_1 : (twinPrimeSegment 352911405 352976941).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 352911405 ≤ 352944173)
    (by decide : 352944173 ≤ 352976941) block2 block3

theorem join_1_0 : (twinPrimeSegment 352845869 352976941).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 352845869 ≤ 352911405)
    (by decide : 352911405 ≤ 352976941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 352845869 352976941).card = 421 := join_1_0

end S168C04
end Sude.GeneratedTwinScan
