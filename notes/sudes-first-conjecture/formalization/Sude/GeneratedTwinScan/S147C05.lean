import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17577)) 308936749 308969517 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 308936749 308969517).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17577 308936749 308969517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17578)) 308969517 309002285 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 308969517 309002285).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17578 308969517 309002285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17579)) 309002285 309035053 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 309002285 309035053).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17579 309002285 309035053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17580)) 309035053 309067821 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 309035053 309067821).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17580 309035053 309067821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 308936749 309002285).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 308936749 ≤ 308969517)
    (by decide : 308969517 ≤ 309002285) block0 block1

theorem join_0_1 : (twinPrimeSegment 309002285 309067821).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 309002285 ≤ 309035053)
    (by decide : 309035053 ≤ 309067821) block2 block3

theorem join_1_0 : (twinPrimeSegment 308936749 309067821).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 308936749 ≤ 309002285)
    (by decide : 309002285 ≤ 309067821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 308936749 309067821).card = 466 := join_1_0

end S147C05
end Sude.GeneratedTwinScan
