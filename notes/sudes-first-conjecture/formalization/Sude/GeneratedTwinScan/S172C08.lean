import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19020)) 361758765 361791533 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 361758765 361791533).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19020 361758765 361791533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19021)) 361791533 361824301 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 361791533 361824301).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19021 361791533 361824301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19022)) 361824301 361857069 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 361824301 361857069).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19022 361824301 361857069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19023)) 361857069 361889837 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 361857069 361889837).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19023 361857069 361889837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 361758765 361824301).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 361758765 ≤ 361791533)
    (by decide : 361791533 ≤ 361824301) block0 block1

theorem join_0_1 : (twinPrimeSegment 361824301 361889837).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 361824301 ≤ 361857069)
    (by decide : 361857069 ≤ 361889837) block2 block3

theorem join_1_0 : (twinPrimeSegment 361758765 361889837).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 361758765 ≤ 361824301)
    (by decide : 361824301 ≤ 361889837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 361758765 361889837).card = 445 := join_1_0

end S172C08
end Sude.GeneratedTwinScan
