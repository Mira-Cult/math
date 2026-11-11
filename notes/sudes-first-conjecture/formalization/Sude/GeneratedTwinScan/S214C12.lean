import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21222)) 450363437 450396205 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 450363437 450396205).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21222 450363437 450396205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21223)) 450396205 450428973 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 450396205 450428973).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21223 450396205 450428973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21224)) 450428973 450461741 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 450428973 450461741).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21224 450428973 450461741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21224)) 450461741 450494509 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 450461741 450494509).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21224 450461741 450494509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 450363437 450428973).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 450363437 ≤ 450396205)
    (by decide : 450396205 ≤ 450428973) block0 block1

theorem join_0_1 : (twinPrimeSegment 450428973 450494509).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 450428973 ≤ 450461741)
    (by decide : 450461741 ≤ 450494509) block2 block3

theorem join_1_0 : (twinPrimeSegment 450363437 450494509).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 450363437 ≤ 450428973)
    (by decide : 450428973 ≤ 450494509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 450363437 450494509).card = 435 := join_1_0

end S214C12
end Sude.GeneratedTwinScan
