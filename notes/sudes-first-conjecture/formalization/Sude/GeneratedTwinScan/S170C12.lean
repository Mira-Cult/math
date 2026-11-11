import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18924)) 358088749 358121517 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 358088749 358121517).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18924 358088749 358121517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18924)) 358121517 358154285 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 358121517 358154285).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18924 358121517 358154285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18925)) 358154285 358187053 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 358154285 358187053).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18925 358154285 358187053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18926)) 358187053 358219821 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 358187053 358219821).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18926 358187053 358219821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 358088749 358154285).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 358088749 ≤ 358121517)
    (by decide : 358121517 ≤ 358154285) block0 block1

theorem join_0_1 : (twinPrimeSegment 358154285 358219821).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 358154285 ≤ 358187053)
    (by decide : 358187053 ≤ 358219821) block2 block3

theorem join_1_0 : (twinPrimeSegment 358088749 358219821).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 358088749 ≤ 358154285)
    (by decide : 358154285 ≤ 358219821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 358088749 358219821).card = 433 := join_1_0

end S170C12
end Sude.GeneratedTwinScan
