import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19079)) 363986989 364019757 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 363986989 364019757).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19079 363986989 364019757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19080)) 364019757 364052525 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 364019757 364052525).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19080 364019757 364052525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19081)) 364052525 364085293 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 364052525 364085293).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19081 364052525 364085293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19081)) 364085293 364118061 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 364085293 364118061).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19081 364085293 364118061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 363986989 364052525).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 363986989 ≤ 364019757)
    (by decide : 364019757 ≤ 364052525) block0 block1

theorem join_0_1 : (twinPrimeSegment 364052525 364118061).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 364052525 ≤ 364085293)
    (by decide : 364085293 ≤ 364118061) block2 block3

theorem join_1_0 : (twinPrimeSegment 363986989 364118061).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 363986989 ≤ 364052525)
    (by decide : 364052525 ≤ 364118061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 363986989 364118061).card = 453 := join_1_0

end S173C09
end Sude.GeneratedTwinScan
