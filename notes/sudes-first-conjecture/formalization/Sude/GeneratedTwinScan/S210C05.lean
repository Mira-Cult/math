import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S210C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21002)) 441057325 441090093 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 441057325 441090093).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21002 441057325 441090093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21002)) 441090093 441122861 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 441090093 441122861).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21002 441090093 441122861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21003)) 441122861 441155629 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 441122861 441155629).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21003 441122861 441155629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21004)) 441155629 441188397 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 441155629 441188397).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21004 441155629 441188397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 441057325 441122861).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 441057325 ≤ 441090093)
    (by decide : 441090093 ≤ 441122861) block0 block1

theorem join_0_1 : (twinPrimeSegment 441122861 441188397).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 441122861 ≤ 441155629)
    (by decide : 441155629 ≤ 441188397) block2 block3

theorem join_1_0 : (twinPrimeSegment 441057325 441188397).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 441057325 ≤ 441122861)
    (by decide : 441122861 ≤ 441188397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 441057325 441188397).card = 444 := join_1_0

end S210C05
end Sude.GeneratedTwinScan
