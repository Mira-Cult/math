import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16603)) 275644461 275677229 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 275644461 275677229).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16603 275644461 275677229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16604)) 275677229 275709997 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 275677229 275709997).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16604 275677229 275709997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16605)) 275709997 275742765 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 275709997 275742765).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16605 275709997 275742765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16606)) 275742765 275775533 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 275742765 275775533).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16606 275742765 275775533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 275644461 275709997).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 275644461 ≤ 275677229)
    (by decide : 275677229 ≤ 275709997) block0 block1

theorem join_0_1 : (twinPrimeSegment 275709997 275775533).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 275709997 ≤ 275742765)
    (by decide : 275742765 ≤ 275775533) block2 block3

theorem join_1_0 : (twinPrimeSegment 275644461 275775533).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 275644461 ≤ 275709997)
    (by decide : 275709997 ≤ 275775533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 275644461 275775533).card = 460 := join_1_0

end S131C07
end Sude.GeneratedTwinScan
