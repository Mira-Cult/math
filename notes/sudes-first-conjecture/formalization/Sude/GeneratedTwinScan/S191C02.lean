import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20021)) 400818221 400850989 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 400818221 400850989).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20021 400818221 400850989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20022)) 400850989 400883757 = 87 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 400850989 400883757).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20022 400850989 400883757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20022)) 400883757 400916525 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 400883757 400916525).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20022 400883757 400916525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20023)) 400916525 400949293 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 400916525 400949293).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20023 400916525 400949293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 400818221 400883757).card = 186 := by
  simpa using combineTwinPrimeSegments (by decide : 400818221 ≤ 400850989)
    (by decide : 400850989 ≤ 400883757) block0 block1

theorem join_0_1 : (twinPrimeSegment 400883757 400949293).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 400883757 ≤ 400916525)
    (by decide : 400916525 ≤ 400949293) block2 block3

theorem join_1_0 : (twinPrimeSegment 400818221 400949293).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 400818221 ≤ 400883757)
    (by decide : 400883757 ≤ 400949293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 400818221 400949293).card = 426 := join_1_0

end S191C02
end Sude.GeneratedTwinScan
