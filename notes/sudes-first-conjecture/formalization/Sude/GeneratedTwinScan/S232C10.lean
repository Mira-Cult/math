import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22088)) 487850029 487882797 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 487850029 487882797).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22088 487850029 487882797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22088)) 487882797 487915565 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 487882797 487915565).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22088 487882797 487915565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22089)) 487915565 487948333 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 487915565 487948333).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22089 487915565 487948333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22090)) 487948333 487981101 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 487948333 487981101).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22090 487948333 487981101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 487850029 487915565).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 487850029 ≤ 487882797)
    (by decide : 487882797 ≤ 487915565) block0 block1

theorem join_0_1 : (twinPrimeSegment 487915565 487981101).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 487915565 ≤ 487948333)
    (by decide : 487948333 ≤ 487981101) block2 block3

theorem join_1_0 : (twinPrimeSegment 487850029 487981101).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 487850029 ≤ 487915565)
    (by decide : 487915565 ≤ 487981101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 487850029 487981101).card = 437 := join_1_0

end S232C10
end Sude.GeneratedTwinScan
