import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14432)) 208273453 208306221 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 208273453 208306221).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14432 208273453 208306221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14433)) 208306221 208338989 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 208306221 208338989).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14433 208306221 208338989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14435)) 208338989 208371757 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 208338989 208371757).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14435 208338989 208371757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14436)) 208371757 208404525 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 208371757 208404525).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14436 208371757 208404525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 208273453 208338989).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 208273453 ≤ 208306221)
    (by decide : 208306221 ≤ 208338989) block0 block1

theorem join_0_1 : (twinPrimeSegment 208338989 208404525).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 208338989 ≤ 208371757)
    (by decide : 208371757 ≤ 208404525) block2 block3

theorem join_1_0 : (twinPrimeSegment 208273453 208404525).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 208273453 ≤ 208338989)
    (by decide : 208338989 ≤ 208404525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 208273453 208404525).card = 469 := join_1_0

end S099C05
end Sude.GeneratedTwinScan
