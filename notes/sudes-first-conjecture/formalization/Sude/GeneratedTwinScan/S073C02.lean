import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12384)) 153354285 153387053 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 153354285 153387053).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12384 153354285 153387053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12386)) 153387053 153419821 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 153387053 153419821).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12386 153387053 153419821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12387)) 153419821 153452589 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 153419821 153452589).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12387 153419821 153452589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12388)) 153452589 153485357 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 153452589 153485357).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12388 153452589 153485357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 153354285 153419821).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 153354285 ≤ 153387053)
    (by decide : 153387053 ≤ 153419821) block0 block1

theorem join_0_1 : (twinPrimeSegment 153419821 153485357).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 153419821 ≤ 153452589)
    (by decide : 153452589 ≤ 153485357) block2 block3

theorem join_1_0 : (twinPrimeSegment 153354285 153485357).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 153354285 ≤ 153419821)
    (by decide : 153419821 ≤ 153485357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 153354285 153485357).card = 506 := join_1_0

end S073C02
end Sude.GeneratedTwinScan
