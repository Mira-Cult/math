import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18736)) 351010861 351043629 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 351010861 351043629).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18736 351010861 351043629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18737)) 351043629 351076397 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 351043629 351076397).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18737 351043629 351076397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18737)) 351076397 351109165 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 351076397 351109165).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18737 351076397 351109165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18738)) 351109165 351141933 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 351109165 351141933).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18738 351109165 351141933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 351010861 351076397).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 351010861 ≤ 351043629)
    (by decide : 351043629 ≤ 351076397) block0 block1

theorem join_0_1 : (twinPrimeSegment 351076397 351141933).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 351076397 ≤ 351109165)
    (by decide : 351109165 ≤ 351141933) block2 block3

theorem join_1_0 : (twinPrimeSegment 351010861 351141933).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 351010861 ≤ 351076397)
    (by decide : 351076397 ≤ 351141933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 351010861 351141933).card = 429 := join_1_0

end S167C06
end Sude.GeneratedTwinScan
