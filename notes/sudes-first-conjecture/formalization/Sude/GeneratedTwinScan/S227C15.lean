import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21864)) 478019629 478052397 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 478019629 478052397).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21864 478019629 478052397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21865)) 478052397 478085165 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 478052397 478085165).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21865 478052397 478085165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21865)) 478085165 478117933 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 478085165 478117933).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21865 478085165 478117933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21866)) 478117933 478150701 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 478117933 478150701).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21866 478117933 478150701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 478019629 478085165).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 478019629 ≤ 478052397)
    (by decide : 478052397 ≤ 478085165) block0 block1

theorem join_0_1 : (twinPrimeSegment 478085165 478150701).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 478085165 ≤ 478117933)
    (by decide : 478117933 ≤ 478150701) block2 block3

theorem join_1_0 : (twinPrimeSegment 478019629 478150701).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 478019629 ≤ 478085165)
    (by decide : 478085165 ≤ 478150701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 478019629 478150701).card = 422 := join_1_0

end S227C15
end Sude.GeneratedTwinScan
