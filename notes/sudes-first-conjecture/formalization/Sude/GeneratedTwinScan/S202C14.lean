import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20627)) 425459757 425492525 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 425459757 425492525).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20627 425459757 425492525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20628)) 425492525 425525293 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 425492525 425525293).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20628 425492525 425525293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20629)) 425525293 425558061 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 425525293 425558061).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20629 425525293 425558061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20629)) 425558061 425590829 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 425558061 425590829).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20629 425558061 425590829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 425459757 425525293).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 425459757 ≤ 425492525)
    (by decide : 425492525 ≤ 425525293) block0 block1

theorem join_0_1 : (twinPrimeSegment 425525293 425590829).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 425525293 ≤ 425558061)
    (by decide : 425558061 ≤ 425590829) block2 block3

theorem join_1_0 : (twinPrimeSegment 425459757 425590829).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 425459757 ≤ 425525293)
    (by decide : 425525293 ≤ 425590829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 425459757 425590829).card = 440 := join_1_0

end S202C14
end Sude.GeneratedTwinScan
