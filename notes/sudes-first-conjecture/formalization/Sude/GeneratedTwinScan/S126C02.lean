import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16264)) 264503341 264536109 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 264503341 264536109).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16264 264503341 264536109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16265)) 264536109 264568877 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 264536109 264568877).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16265 264536109 264568877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16266)) 264568877 264601645 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 264568877 264601645).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16266 264568877 264601645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16267)) 264601645 264634413 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 264601645 264634413).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16267 264601645 264634413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 264503341 264568877).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 264503341 ≤ 264536109)
    (by decide : 264536109 ≤ 264568877) block0 block1

theorem join_0_1 : (twinPrimeSegment 264568877 264634413).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 264568877 ≤ 264601645)
    (by decide : 264601645 ≤ 264634413) block2 block3

theorem join_1_0 : (twinPrimeSegment 264503341 264634413).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 264503341 ≤ 264568877)
    (by decide : 264568877 ≤ 264634413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 264503341 264634413).card = 466 := join_1_0

end S126C02
end Sude.GeneratedTwinScan
