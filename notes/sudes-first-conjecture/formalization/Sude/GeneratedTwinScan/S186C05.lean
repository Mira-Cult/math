import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19767)) 390725677 390758445 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 390725677 390758445).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19767 390725677 390758445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19768)) 390758445 390791213 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 390758445 390791213).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19768 390758445 390791213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19769)) 390791213 390823981 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 390791213 390823981).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19769 390791213 390823981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19770)) 390823981 390856749 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 390823981 390856749).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19770 390823981 390856749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 390725677 390791213).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 390725677 ≤ 390758445)
    (by decide : 390758445 ≤ 390791213) block0 block1

theorem join_0_1 : (twinPrimeSegment 390791213 390856749).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 390791213 ≤ 390823981)
    (by decide : 390823981 ≤ 390856749) block2 block3

theorem join_1_0 : (twinPrimeSegment 390725677 390856749).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 390725677 ≤ 390791213)
    (by decide : 390791213 ≤ 390856749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 390725677 390856749).card = 470 := join_1_0

end S186C05
end Sude.GeneratedTwinScan
