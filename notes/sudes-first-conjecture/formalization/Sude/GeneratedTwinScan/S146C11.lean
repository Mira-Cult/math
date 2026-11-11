import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17540)) 307626029 307658797 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 307626029 307658797).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17540 307626029 307658797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17541)) 307658797 307691565 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 307658797 307691565).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17541 307658797 307691565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17542)) 307691565 307724333 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 307691565 307724333).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17542 307691565 307724333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17543)) 307724333 307757101 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 307724333 307757101).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17543 307724333 307757101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 307626029 307691565).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 307626029 ≤ 307658797)
    (by decide : 307658797 ≤ 307691565) block0 block1

theorem join_0_1 : (twinPrimeSegment 307691565 307757101).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 307691565 ≤ 307724333)
    (by decide : 307724333 ≤ 307757101) block2 block3

theorem join_1_0 : (twinPrimeSegment 307626029 307757101).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 307626029 ≤ 307691565)
    (by decide : 307691565 ≤ 307757101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 307626029 307757101).card = 447 := join_1_0

end S146C11
end Sude.GeneratedTwinScan
