import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18840)) 354943021 354975789 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 354943021 354975789).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18840 354943021 354975789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18841)) 354975789 355008557 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 354975789 355008557).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18841 354975789 355008557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18842)) 355008557 355041325 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 355008557 355041325).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18842 355008557 355041325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18843)) 355041325 355074093 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 355041325 355074093).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18843 355041325 355074093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 354943021 355008557).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 354943021 ≤ 354975789)
    (by decide : 354975789 ≤ 355008557) block0 block1

theorem join_0_1 : (twinPrimeSegment 355008557 355074093).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 355008557 ≤ 355041325)
    (by decide : 355041325 ≤ 355074093) block2 block3

theorem join_1_0 : (twinPrimeSegment 354943021 355074093).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 354943021 ≤ 355008557)
    (by decide : 355008557 ≤ 355074093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 354943021 355074093).card = 473 := join_1_0

end S169C04
end Sude.GeneratedTwinScan
