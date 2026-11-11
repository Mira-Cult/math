import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19240)) 370147373 370180141 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 370147373 370180141).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19240 370147373 370180141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19240)) 370180141 370212909 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 370180141 370212909).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19240 370180141 370212909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19241)) 370212909 370245677 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 370212909 370245677).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19241 370212909 370245677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19242)) 370245677 370278445 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 370245677 370278445).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19242 370245677 370278445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 370147373 370212909).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 370147373 ≤ 370180141)
    (by decide : 370180141 ≤ 370212909) block0 block1

theorem join_0_1 : (twinPrimeSegment 370212909 370278445).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 370212909 ≤ 370245677)
    (by decide : 370245677 ≤ 370278445) block2 block3

theorem join_1_0 : (twinPrimeSegment 370147373 370278445).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 370147373 ≤ 370212909)
    (by decide : 370212909 ≤ 370278445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 370147373 370278445).card = 458 := join_1_0

end S176C08
end Sude.GeneratedTwinScan
