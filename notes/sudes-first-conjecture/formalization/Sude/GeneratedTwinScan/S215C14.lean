import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21278)) 452722733 452755501 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 452722733 452755501).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21278 452722733 452755501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21278)) 452755501 452788269 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 452755501 452788269).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21278 452755501 452788269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21279)) 452788269 452821037 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 452788269 452821037).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21279 452788269 452821037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21280)) 452821037 452853805 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 452821037 452853805).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21280 452821037 452853805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 452722733 452788269).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 452722733 ≤ 452755501)
    (by decide : 452755501 ≤ 452788269) block0 block1

theorem join_0_1 : (twinPrimeSegment 452788269 452853805).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 452788269 ≤ 452821037)
    (by decide : 452821037 ≤ 452853805) block2 block3

theorem join_1_0 : (twinPrimeSegment 452722733 452853805).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 452722733 ≤ 452788269)
    (by decide : 452788269 ≤ 452853805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 452722733 452853805).card = 444 := join_1_0

end S215C14
end Sude.GeneratedTwinScan
