import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13787)) 190054445 190087213 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 190054445 190087213).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13787 190054445 190087213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13788)) 190087213 190119981 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 190087213 190119981).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13788 190087213 190119981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13789)) 190119981 190152749 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 190119981 190152749).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13789 190119981 190152749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13790)) 190152749 190185517 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 190152749 190185517).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13790 190152749 190185517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 190054445 190119981).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 190054445 ≤ 190087213)
    (by decide : 190087213 ≤ 190119981) block0 block1

theorem join_0_1 : (twinPrimeSegment 190119981 190185517).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 190119981 ≤ 190152749)
    (by decide : 190152749 ≤ 190185517) block2 block3

theorem join_1_0 : (twinPrimeSegment 190054445 190185517).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 190054445 ≤ 190119981)
    (by decide : 190119981 ≤ 190185517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 190054445 190185517).card = 478 := join_1_0

end S090C10
end Sude.GeneratedTwinScan
