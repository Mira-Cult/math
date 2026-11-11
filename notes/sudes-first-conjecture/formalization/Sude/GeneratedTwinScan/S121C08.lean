import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15963)) 254804013 254836781 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 254804013 254836781).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15963 254804013 254836781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15964)) 254836781 254869549 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 254836781 254869549).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15964 254836781 254869549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15965)) 254869549 254902317 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 254869549 254902317).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15965 254869549 254902317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15966)) 254902317 254935085 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 254902317 254935085).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15966 254902317 254935085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 254804013 254869549).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 254804013 ≤ 254836781)
    (by decide : 254836781 ≤ 254869549) block0 block1

theorem join_0_1 : (twinPrimeSegment 254869549 254935085).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 254869549 ≤ 254902317)
    (by decide : 254902317 ≤ 254935085) block2 block3

theorem join_1_0 : (twinPrimeSegment 254804013 254935085).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 254804013 ≤ 254869549)
    (by decide : 254869549 ≤ 254935085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 254804013 254935085).card = 489 := join_1_0

end S121C08
end Sude.GeneratedTwinScan
