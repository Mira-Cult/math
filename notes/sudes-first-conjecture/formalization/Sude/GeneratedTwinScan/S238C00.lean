import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22341)) 499122221 499154989 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 499122221 499154989).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22341 499122221 499154989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22342)) 499154989 499187757 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 499154989 499187757).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22342 499154989 499187757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22343)) 499187757 499220525 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 499187757 499220525).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22343 499187757 499220525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22343)) 499220525 499253293 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 499220525 499253293).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22343 499220525 499253293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 499122221 499187757).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 499122221 ≤ 499154989)
    (by decide : 499154989 ≤ 499187757) block0 block1

theorem join_0_1 : (twinPrimeSegment 499187757 499253293).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 499187757 ≤ 499220525)
    (by decide : 499220525 ≤ 499253293) block2 block3

theorem join_1_0 : (twinPrimeSegment 499122221 499253293).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 499122221 ≤ 499187757)
    (by decide : 499187757 ≤ 499253293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 499122221 499253293).card = 438 := join_1_0

end S238C00
end Sude.GeneratedTwinScan
