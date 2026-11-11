import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21786)) 474611757 474644525 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 474611757 474644525).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21786 474611757 474644525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21787)) 474644525 474677293 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 474644525 474677293).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21787 474644525 474677293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21787)) 474677293 474710061 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 474677293 474710061).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21787 474677293 474710061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21788)) 474710061 474742829 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 474710061 474742829).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21788 474710061 474742829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 474611757 474677293).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 474611757 ≤ 474644525)
    (by decide : 474644525 ≤ 474677293) block0 block1

theorem join_0_1 : (twinPrimeSegment 474677293 474742829).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 474677293 ≤ 474710061)
    (by decide : 474710061 ≤ 474742829) block2 block3

theorem join_1_0 : (twinPrimeSegment 474611757 474742829).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 474611757 ≤ 474677293)
    (by decide : 474677293 ≤ 474742829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 474611757 474742829).card = 432 := join_1_0

end S226C05
end Sude.GeneratedTwinScan
