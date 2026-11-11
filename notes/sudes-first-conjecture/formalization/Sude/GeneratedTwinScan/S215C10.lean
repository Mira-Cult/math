import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21265)) 452198445 452231213 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 452198445 452231213).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21265 452198445 452231213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21266)) 452231213 452263981 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 452231213 452263981).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21266 452231213 452263981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21267)) 452263981 452296749 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 452263981 452296749).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21267 452263981 452296749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21268)) 452296749 452329517 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 452296749 452329517).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21268 452296749 452329517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 452198445 452263981).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 452198445 ≤ 452231213)
    (by decide : 452231213 ≤ 452263981) block0 block1

theorem join_0_1 : (twinPrimeSegment 452263981 452329517).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 452263981 ≤ 452296749)
    (by decide : 452296749 ≤ 452329517) block2 block3

theorem join_1_0 : (twinPrimeSegment 452198445 452329517).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 452198445 ≤ 452263981)
    (by decide : 452263981 ≤ 452329517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 452198445 452329517).card = 443 := join_1_0

end S215C10
end Sude.GeneratedTwinScan
