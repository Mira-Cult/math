import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21281)) 452853805 452886573 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 452853805 452886573).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21281 452853805 452886573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21281)) 452886573 452919341 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 452886573 452919341).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21281 452886573 452919341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21282)) 452919341 452952109 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 452919341 452952109).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21282 452919341 452952109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21283)) 452952109 452984877 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 452952109 452984877).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21283 452952109 452984877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 452853805 452919341).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 452853805 ≤ 452886573)
    (by decide : 452886573 ≤ 452919341) block0 block1

theorem join_0_1 : (twinPrimeSegment 452919341 452984877).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 452919341 ≤ 452952109)
    (by decide : 452952109 ≤ 452984877) block2 block3

theorem join_1_0 : (twinPrimeSegment 452853805 452984877).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 452853805 ≤ 452919341)
    (by decide : 452919341 ≤ 452984877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 452853805 452984877).card = 435 := join_1_0

end S215C15
end Sude.GeneratedTwinScan
