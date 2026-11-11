import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22200)) 492830765 492863533 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 492830765 492863533).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22200 492830765 492863533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22201)) 492863533 492896301 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 492863533 492896301).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22201 492863533 492896301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22202)) 492896301 492929069 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 492896301 492929069).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22202 492896301 492929069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22202)) 492929069 492961837 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 492929069 492961837).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22202 492929069 492961837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 492830765 492896301).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 492830765 ≤ 492863533)
    (by decide : 492863533 ≤ 492896301) block0 block1

theorem join_0_1 : (twinPrimeSegment 492896301 492961837).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 492896301 ≤ 492929069)
    (by decide : 492929069 ≤ 492961837) block2 block3

theorem join_1_0 : (twinPrimeSegment 492830765 492961837).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 492830765 ≤ 492896301)
    (by decide : 492896301 ≤ 492961837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 492830765 492961837).card = 431 := join_1_0

end S235C00
end Sude.GeneratedTwinScan
