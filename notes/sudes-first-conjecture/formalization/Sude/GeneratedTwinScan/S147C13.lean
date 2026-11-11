import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17607)) 309985325 310018093 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 309985325 310018093).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17607 309985325 310018093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17608)) 310018093 310050861 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 310018093 310050861).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17608 310018093 310050861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17609)) 310050861 310083629 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 310050861 310083629).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17609 310050861 310083629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17610)) 310083629 310116397 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 310083629 310116397).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17610 310083629 310116397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 309985325 310050861).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 309985325 ≤ 310018093)
    (by decide : 310018093 ≤ 310050861) block0 block1

theorem join_0_1 : (twinPrimeSegment 310050861 310116397).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 310050861 ≤ 310083629)
    (by decide : 310083629 ≤ 310116397) block2 block3

theorem join_1_0 : (twinPrimeSegment 309985325 310116397).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 309985325 ≤ 310050861)
    (by decide : 310050861 ≤ 310116397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 309985325 310116397).card = 426 := join_1_0

end S147C13
end Sude.GeneratedTwinScan
