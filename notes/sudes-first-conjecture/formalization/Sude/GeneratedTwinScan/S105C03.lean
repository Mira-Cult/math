import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14853)) 220594221 220626989 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 220594221 220626989).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14853 220594221 220626989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14854)) 220626989 220659757 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 220626989 220659757).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14854 220626989 220659757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14855)) 220659757 220692525 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 220659757 220692525).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14855 220659757 220692525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14856)) 220692525 220725293 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 220692525 220725293).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14856 220692525 220725293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 220594221 220659757).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 220594221 ≤ 220626989)
    (by decide : 220626989 ≤ 220659757) block0 block1

theorem join_0_1 : (twinPrimeSegment 220659757 220725293).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 220659757 ≤ 220692525)
    (by decide : 220692525 ≤ 220725293) block2 block3

theorem join_1_0 : (twinPrimeSegment 220594221 220725293).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 220594221 ≤ 220659757)
    (by decide : 220659757 ≤ 220725293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 220594221 220725293).card = 465 := join_1_0

end S105C03
end Sude.GeneratedTwinScan
