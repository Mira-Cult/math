import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22840)) 521666605 521699373 = 89 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 521666605 521699373).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22840 521666605 521699373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22841)) 521699373 521732141 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 521699373 521732141).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22841 521699373 521732141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22842)) 521732141 521764909 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 521732141 521764909).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22842 521732141 521764909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22842)) 521764909 521797677 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 521764909 521797677).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22842 521764909 521797677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 521666605 521732141).card = 194 := by
  simpa using combineTwinPrimeSegments (by decide : 521666605 ≤ 521699373)
    (by decide : 521699373 ≤ 521732141) block0 block1

theorem join_0_1 : (twinPrimeSegment 521732141 521797677).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 521732141 ≤ 521764909)
    (by decide : 521764909 ≤ 521797677) block2 block3

theorem join_1_0 : (twinPrimeSegment 521666605 521797677).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 521666605 ≤ 521732141)
    (by decide : 521732141 ≤ 521797677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 521666605 521797677).card = 413 := join_1_0

end S248C12
end Sude.GeneratedTwinScan
