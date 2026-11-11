import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22610)) 511180845 511213613 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 511180845 511213613).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22610 511180845 511213613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22610)) 511213613 511246381 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 511213613 511246381).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22610 511213613 511246381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22611)) 511246381 511279149 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 511246381 511279149).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22611 511246381 511279149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22612)) 511279149 511311917 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 511279149 511311917).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22612 511279149 511311917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 511180845 511246381).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 511180845 ≤ 511213613)
    (by decide : 511213613 ≤ 511246381) block0 block1

theorem join_0_1 : (twinPrimeSegment 511246381 511311917).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 511246381 ≤ 511279149)
    (by decide : 511279149 ≤ 511311917) block2 block3

theorem join_1_0 : (twinPrimeSegment 511180845 511311917).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 511180845 ≤ 511246381)
    (by decide : 511246381 ≤ 511311917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 511180845 511311917).card = 437 := join_1_0

end S243C12
end Sude.GeneratedTwinScan
