import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22835)) 521404461 521437229 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 521404461 521437229).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22835 521404461 521437229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22835)) 521437229 521469997 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 521437229 521469997).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22835 521437229 521469997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22836)) 521469997 521502765 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 521469997 521502765).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22836 521469997 521502765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22837)) 521502765 521535533 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 521502765 521535533).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22837 521502765 521535533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 521404461 521469997).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 521404461 ≤ 521437229)
    (by decide : 521437229 ≤ 521469997) block0 block1

theorem join_0_1 : (twinPrimeSegment 521469997 521535533).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 521469997 ≤ 521502765)
    (by decide : 521502765 ≤ 521535533) block2 block3

theorem join_1_0 : (twinPrimeSegment 521404461 521535533).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 521404461 ≤ 521469997)
    (by decide : 521469997 ≤ 521535533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 521404461 521535533).card = 423 := join_1_0

end S248C10
end Sude.GeneratedTwinScan
