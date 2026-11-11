import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21268)) 452329517 452362285 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 452329517 452362285).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21268 452329517 452362285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21269)) 452362285 452395053 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 452362285 452395053).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21269 452362285 452395053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21270)) 452395053 452427821 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 452395053 452427821).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21270 452395053 452427821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21271)) 452427821 452460589 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 452427821 452460589).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21271 452427821 452460589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 452329517 452395053).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 452329517 ≤ 452362285)
    (by decide : 452362285 ≤ 452395053) block0 block1

theorem join_0_1 : (twinPrimeSegment 452395053 452460589).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 452395053 ≤ 452427821)
    (by decide : 452427821 ≤ 452460589) block2 block3

theorem join_1_0 : (twinPrimeSegment 452329517 452460589).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 452329517 ≤ 452395053)
    (by decide : 452395053 ≤ 452460589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 452329517 452460589).card = 443 := join_1_0

end S215C11
end Sude.GeneratedTwinScan
