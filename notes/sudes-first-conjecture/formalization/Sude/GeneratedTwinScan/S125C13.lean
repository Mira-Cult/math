import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16244)) 263847981 263880749 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 263847981 263880749).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16244 263847981 263880749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16245)) 263880749 263913517 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 263880749 263913517).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16245 263880749 263913517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16246)) 263913517 263946285 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 263913517 263946285).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16246 263913517 263946285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16247)) 263946285 263979053 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 263946285 263979053).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16247 263946285 263979053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 263847981 263913517).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 263847981 ≤ 263880749)
    (by decide : 263880749 ≤ 263913517) block0 block1

theorem join_0_1 : (twinPrimeSegment 263913517 263979053).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 263913517 ≤ 263946285)
    (by decide : 263946285 ≤ 263979053) block2 block3

theorem join_1_0 : (twinPrimeSegment 263847981 263979053).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 263847981 ≤ 263913517)
    (by decide : 263913517 ≤ 263979053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 263847981 263979053).card = 467 := join_1_0

end S125C13
end Sude.GeneratedTwinScan
