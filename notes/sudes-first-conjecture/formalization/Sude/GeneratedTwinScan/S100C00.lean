import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14482)) 209715245 209748013 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 209715245 209748013).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14482 209715245 209748013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14483)) 209748013 209780781 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 209748013 209780781).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14483 209748013 209780781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14484)) 209780781 209813549 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 209780781 209813549).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14484 209780781 209813549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14486)) 209813549 209846317 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 209813549 209846317).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14486 209813549 209846317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 209715245 209780781).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 209715245 ≤ 209748013)
    (by decide : 209748013 ≤ 209780781) block0 block1

theorem join_0_1 : (twinPrimeSegment 209780781 209846317).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 209780781 ≤ 209813549)
    (by decide : 209813549 ≤ 209846317) block2 block3

theorem join_1_0 : (twinPrimeSegment 209715245 209846317).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 209715245 ≤ 209780781)
    (by decide : 209780781 ≤ 209846317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 209715245 209846317).card = 476 := join_1_0

end S100C00
end Sude.GeneratedTwinScan
