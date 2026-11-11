import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22644)) 512753709 512786477 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 512753709 512786477).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22644 512753709 512786477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22645)) 512786477 512819245 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 512786477 512819245).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22645 512786477 512819245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22646)) 512819245 512852013 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 512819245 512852013).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22646 512819245 512852013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22646)) 512852013 512884781 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 512852013 512884781).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22646 512852013 512884781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 512753709 512819245).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 512753709 ≤ 512786477)
    (by decide : 512786477 ≤ 512819245) block0 block1

theorem join_0_1 : (twinPrimeSegment 512819245 512884781).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 512819245 ≤ 512852013)
    (by decide : 512852013 ≤ 512884781) block2 block3

theorem join_1_0 : (twinPrimeSegment 512753709 512884781).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 512753709 ≤ 512819245)
    (by decide : 512819245 ≤ 512884781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 512753709 512884781).card = 432 := join_1_0

end S244C08
end Sude.GeneratedTwinScan
