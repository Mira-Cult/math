import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13474)) 181534765 181567533 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 181534765 181567533).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13474 181534765 181567533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13475)) 181567533 181600301 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 181567533 181600301).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13475 181567533 181600301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13477)) 181600301 181633069 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 181600301 181633069).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13477 181600301 181633069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13478)) 181633069 181665837 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 181633069 181665837).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13478 181633069 181665837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 181534765 181600301).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 181534765 ≤ 181567533)
    (by decide : 181567533 ≤ 181600301) block0 block1

theorem join_0_1 : (twinPrimeSegment 181600301 181665837).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 181600301 ≤ 181633069)
    (by decide : 181633069 ≤ 181665837) block2 block3

theorem join_1_0 : (twinPrimeSegment 181534765 181665837).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 181534765 ≤ 181600301)
    (by decide : 181600301 ≤ 181665837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 181534765 181665837).card = 480 := join_1_0

end S086C09
end Sude.GeneratedTwinScan
