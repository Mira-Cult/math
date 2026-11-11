import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19379)) 375521325 375554093 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 375521325 375554093).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19379 375521325 375554093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19380)) 375554093 375586861 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 375554093 375586861).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19380 375554093 375586861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19380)) 375586861 375619629 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 375586861 375619629).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19380 375586861 375619629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19381)) 375619629 375652397 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 375619629 375652397).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19381 375619629 375652397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 375521325 375586861).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 375521325 ≤ 375554093)
    (by decide : 375554093 ≤ 375586861) block0 block1

theorem join_0_1 : (twinPrimeSegment 375586861 375652397).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 375586861 ≤ 375619629)
    (by decide : 375619629 ≤ 375652397) block2 block3

theorem join_1_0 : (twinPrimeSegment 375521325 375652397).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 375521325 ≤ 375586861)
    (by decide : 375586861 ≤ 375652397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 375521325 375652397).card = 435 := join_1_0

end S179C01
end Sude.GeneratedTwinScan
