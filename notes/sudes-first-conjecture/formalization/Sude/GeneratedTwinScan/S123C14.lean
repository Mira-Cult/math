import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16118)) 259784749 259817517 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 259784749 259817517).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16118 259784749 259817517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16119)) 259817517 259850285 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 259817517 259850285).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16119 259817517 259850285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16120)) 259850285 259883053 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 259850285 259883053).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16120 259850285 259883053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16121)) 259883053 259915821 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 259883053 259915821).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16121 259883053 259915821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 259784749 259850285).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 259784749 ≤ 259817517)
    (by decide : 259817517 ≤ 259850285) block0 block1

theorem join_0_1 : (twinPrimeSegment 259850285 259915821).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 259850285 ≤ 259883053)
    (by decide : 259883053 ≤ 259915821) block2 block3

theorem join_1_0 : (twinPrimeSegment 259784749 259915821).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 259784749 ≤ 259850285)
    (by decide : 259850285 ≤ 259915821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 259784749 259915821).card = 445 := join_1_0

end S123C14
end Sude.GeneratedTwinScan
