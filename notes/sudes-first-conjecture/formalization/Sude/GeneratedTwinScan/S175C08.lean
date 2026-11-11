import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19185)) 368050221 368082989 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 368050221 368082989).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19185 368050221 368082989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19186)) 368082989 368115757 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 368082989 368115757).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19186 368082989 368115757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19187)) 368115757 368148525 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 368115757 368148525).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19187 368115757 368148525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19188)) 368148525 368181293 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 368148525 368181293).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19188 368148525 368181293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 368050221 368115757).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 368050221 ≤ 368082989)
    (by decide : 368082989 ≤ 368115757) block0 block1

theorem join_0_1 : (twinPrimeSegment 368115757 368181293).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 368115757 ≤ 368148525)
    (by decide : 368148525 ≤ 368181293) block2 block3

theorem join_1_0 : (twinPrimeSegment 368050221 368181293).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 368050221 ≤ 368115757)
    (by decide : 368115757 ≤ 368181293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 368050221 368181293).card = 460 := join_1_0

end S175C08
end Sude.GeneratedTwinScan
