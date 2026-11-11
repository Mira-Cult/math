import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14074)) 198049837 198082605 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 198049837 198082605).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14074 198049837 198082605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14075)) 198082605 198115373 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 198082605 198115373).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14075 198082605 198115373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14076)) 198115373 198148141 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 198115373 198148141).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14076 198115373 198148141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14077)) 198148141 198180909 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 198148141 198180909).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14077 198148141 198180909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 198049837 198115373).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 198049837 ≤ 198082605)
    (by decide : 198082605 ≤ 198115373) block0 block1

theorem join_0_1 : (twinPrimeSegment 198115373 198180909).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 198115373 ≤ 198148141)
    (by decide : 198148141 ≤ 198180909) block2 block3

theorem join_1_0 : (twinPrimeSegment 198049837 198180909).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 198049837 ≤ 198115373)
    (by decide : 198115373 ≤ 198180909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 198049837 198180909).card = 453 := join_1_0

end S094C07
end Sude.GeneratedTwinScan
