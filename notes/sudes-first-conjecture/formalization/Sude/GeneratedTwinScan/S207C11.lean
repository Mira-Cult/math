import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20870)) 435552301 435585069 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 435552301 435585069).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20870 435552301 435585069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20871)) 435585069 435617837 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 435585069 435617837).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20871 435585069 435617837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20872)) 435617837 435650605 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 435617837 435650605).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20872 435617837 435650605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20873)) 435650605 435683373 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 435650605 435683373).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20873 435650605 435683373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 435552301 435617837).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 435552301 ≤ 435585069)
    (by decide : 435585069 ≤ 435617837) block0 block1

theorem join_0_1 : (twinPrimeSegment 435617837 435683373).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 435617837 ≤ 435650605)
    (by decide : 435650605 ≤ 435683373) block2 block3

theorem join_1_0 : (twinPrimeSegment 435552301 435683373).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 435552301 ≤ 435617837)
    (by decide : 435617837 ≤ 435683373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 435552301 435683373).card = 477 := join_1_0

end S207C11
end Sude.GeneratedTwinScan
