import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21801)) 475267117 475299885 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 475267117 475299885).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21801 475267117 475299885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21802)) 475299885 475332653 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 475299885 475332653).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21802 475299885 475332653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21802)) 475332653 475365421 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 475332653 475365421).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21802 475332653 475365421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21803)) 475365421 475398189 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 475365421 475398189).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21803 475365421 475398189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 475267117 475332653).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 475267117 ≤ 475299885)
    (by decide : 475299885 ≤ 475332653) block0 block1

theorem join_0_1 : (twinPrimeSegment 475332653 475398189).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 475332653 ≤ 475365421)
    (by decide : 475365421 ≤ 475398189) block2 block3

theorem join_1_0 : (twinPrimeSegment 475267117 475398189).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 475267117 ≤ 475332653)
    (by decide : 475332653 ≤ 475398189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 475267117 475398189).card = 455 := join_1_0

end S226C10
end Sude.GeneratedTwinScan
