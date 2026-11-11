import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17670)) 312213549 312246317 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 312213549 312246317).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17670 312213549 312246317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17671)) 312246317 312279085 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 312246317 312279085).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17671 312246317 312279085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17672)) 312279085 312311853 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 312279085 312311853).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17672 312279085 312311853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17673)) 312311853 312344621 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 312311853 312344621).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17673 312311853 312344621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 312213549 312279085).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 312213549 ≤ 312246317)
    (by decide : 312246317 ≤ 312279085) block0 block1

theorem join_0_1 : (twinPrimeSegment 312279085 312344621).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 312279085 ≤ 312311853)
    (by decide : 312311853 ≤ 312344621) block2 block3

theorem join_1_0 : (twinPrimeSegment 312213549 312344621).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 312213549 ≤ 312279085)
    (by decide : 312279085 ≤ 312344621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 312213549 312344621).card = 459 := join_1_0

end S148C14
end Sude.GeneratedTwinScan
