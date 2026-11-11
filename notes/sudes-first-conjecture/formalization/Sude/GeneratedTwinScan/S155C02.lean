import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18037)) 325320749 325353517 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 325320749 325353517).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18037 325320749 325353517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18038)) 325353517 325386285 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 325353517 325386285).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18038 325353517 325386285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18039)) 325386285 325419053 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 325386285 325419053).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18039 325386285 325419053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18040)) 325419053 325451821 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 325419053 325451821).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18040 325419053 325451821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 325320749 325386285).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 325320749 ≤ 325353517)
    (by decide : 325353517 ≤ 325386285) block0 block1

theorem join_0_1 : (twinPrimeSegment 325386285 325451821).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 325386285 ≤ 325419053)
    (by decide : 325419053 ≤ 325451821) block2 block3

theorem join_1_0 : (twinPrimeSegment 325320749 325451821).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 325320749 ≤ 325386285)
    (by decide : 325386285 ≤ 325451821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 325320749 325451821).card = 438 := join_1_0

end S155C02
end Sude.GeneratedTwinScan
