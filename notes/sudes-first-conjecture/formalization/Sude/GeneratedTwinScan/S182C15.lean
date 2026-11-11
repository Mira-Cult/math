import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19587)) 383647789 383680557 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 383647789 383680557).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19587 383647789 383680557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19588)) 383680557 383713325 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 383680557 383713325).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19588 383680557 383713325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19589)) 383713325 383746093 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 383713325 383746093).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19589 383713325 383746093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19590)) 383746093 383778861 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 383746093 383778861).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19590 383746093 383778861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 383647789 383713325).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 383647789 ≤ 383680557)
    (by decide : 383680557 ≤ 383713325) block0 block1

theorem join_0_1 : (twinPrimeSegment 383713325 383778861).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 383713325 ≤ 383746093)
    (by decide : 383746093 ≤ 383778861) block2 block3

theorem join_1_0 : (twinPrimeSegment 383647789 383778861).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 383647789 ≤ 383713325)
    (by decide : 383713325 ≤ 383778861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 383647789 383778861).card = 453 := join_1_0

end S182C15
end Sude.GeneratedTwinScan
