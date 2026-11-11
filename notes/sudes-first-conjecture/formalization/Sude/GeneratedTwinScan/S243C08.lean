import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22598)) 510656557 510689325 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 510656557 510689325).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22598 510656557 510689325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22599)) 510689325 510722093 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 510689325 510722093).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22599 510689325 510722093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22599)) 510722093 510754861 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 510722093 510754861).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22599 510722093 510754861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22600)) 510754861 510787629 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 510754861 510787629).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22600 510754861 510787629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 510656557 510722093).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 510656557 ≤ 510689325)
    (by decide : 510689325 ≤ 510722093) block0 block1

theorem join_0_1 : (twinPrimeSegment 510722093 510787629).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 510722093 ≤ 510754861)
    (by decide : 510754861 ≤ 510787629) block2 block3

theorem join_1_0 : (twinPrimeSegment 510656557 510787629).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 510656557 ≤ 510722093)
    (by decide : 510722093 ≤ 510787629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 510656557 510787629).card = 416 := join_1_0

end S243C08
end Sude.GeneratedTwinScan
