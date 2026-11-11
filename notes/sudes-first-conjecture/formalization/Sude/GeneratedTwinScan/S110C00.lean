import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15189)) 230686765 230719533 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 230686765 230719533).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15189 230686765 230719533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15190)) 230719533 230752301 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 230719533 230752301).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15190 230719533 230752301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15191)) 230752301 230785069 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 230752301 230785069).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15191 230752301 230785069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15192)) 230785069 230817837 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 230785069 230817837).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15192 230785069 230817837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 230686765 230752301).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 230686765 ≤ 230719533)
    (by decide : 230719533 ≤ 230752301) block0 block1

theorem join_0_1 : (twinPrimeSegment 230752301 230817837).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 230752301 ≤ 230785069)
    (by decide : 230785069 ≤ 230817837) block2 block3

theorem join_1_0 : (twinPrimeSegment 230686765 230817837).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 230686765 ≤ 230752301)
    (by decide : 230752301 ≤ 230817837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 230686765 230817837).card = 450 := join_1_0

end S110C00
end Sude.GeneratedTwinScan
