import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22866)) 522846253 522879021 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 522846253 522879021).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22866 522846253 522879021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22867)) 522879021 522911789 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 522879021 522911789).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22867 522879021 522911789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22867)) 522911789 522944557 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 522911789 522944557).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22867 522911789 522944557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22868)) 522944557 522977325 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 522944557 522977325).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22868 522944557 522977325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 522846253 522911789).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 522846253 ≤ 522879021)
    (by decide : 522879021 ≤ 522911789) block0 block1

theorem join_0_1 : (twinPrimeSegment 522911789 522977325).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 522911789 ≤ 522944557)
    (by decide : 522944557 ≤ 522977325) block2 block3

theorem join_1_0 : (twinPrimeSegment 522846253 522977325).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 522846253 ≤ 522911789)
    (by decide : 522911789 ≤ 522977325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 522846253 522977325).card = 414 := join_1_0

end S249C05
end Sude.GeneratedTwinScan
