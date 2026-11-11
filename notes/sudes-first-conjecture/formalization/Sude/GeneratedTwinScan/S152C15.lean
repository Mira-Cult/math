import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17909)) 320733229 320765997 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 320733229 320765997).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17909 320733229 320765997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17910)) 320765997 320798765 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 320765997 320798765).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17910 320765997 320798765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17911)) 320798765 320831533 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 320798765 320831533).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17911 320798765 320831533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17912)) 320831533 320864301 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 320831533 320864301).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17912 320831533 320864301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 320733229 320798765).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 320733229 ≤ 320765997)
    (by decide : 320765997 ≤ 320798765) block0 block1

theorem join_0_1 : (twinPrimeSegment 320798765 320864301).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 320798765 ≤ 320831533)
    (by decide : 320831533 ≤ 320864301) block2 block3

theorem join_1_0 : (twinPrimeSegment 320733229 320864301).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 320733229 ≤ 320798765)
    (by decide : 320798765 ≤ 320864301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 320733229 320864301).card = 460 := join_1_0

end S152C15
end Sude.GeneratedTwinScan
