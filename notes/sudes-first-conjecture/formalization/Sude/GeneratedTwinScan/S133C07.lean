import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16729)) 279838765 279871533 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 279838765 279871533).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16729 279838765 279871533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16730)) 279871533 279904301 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 279871533 279904301).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16730 279871533 279904301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16731)) 279904301 279937069 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 279904301 279937069).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16731 279904301 279937069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16732)) 279937069 279969837 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 279937069 279969837).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16732 279937069 279969837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 279838765 279904301).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 279838765 ≤ 279871533)
    (by decide : 279871533 ≤ 279904301) block0 block1

theorem join_0_1 : (twinPrimeSegment 279904301 279969837).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 279904301 ≤ 279937069)
    (by decide : 279937069 ≤ 279969837) block2 block3

theorem join_1_0 : (twinPrimeSegment 279838765 279969837).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 279838765 ≤ 279904301)
    (by decide : 279904301 ≤ 279969837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 279838765 279969837).card = 460 := join_1_0

end S133C07
end Sude.GeneratedTwinScan
