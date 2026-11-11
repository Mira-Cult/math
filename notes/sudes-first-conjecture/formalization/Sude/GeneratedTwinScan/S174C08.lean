import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19130)) 365953069 365985837 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 365953069 365985837).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19130 365953069 365985837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19131)) 365985837 366018605 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 365985837 366018605).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19131 365985837 366018605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19132)) 366018605 366051373 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 366018605 366051373).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19132 366018605 366051373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19133)) 366051373 366084141 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 366051373 366084141).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19133 366051373 366084141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 365953069 366018605).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 365953069 ≤ 365985837)
    (by decide : 365985837 ≤ 366018605) block0 block1

theorem join_0_1 : (twinPrimeSegment 366018605 366084141).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 366018605 ≤ 366051373)
    (by decide : 366051373 ≤ 366084141) block2 block3

theorem join_1_0 : (twinPrimeSegment 365953069 366084141).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 365953069 ≤ 366018605)
    (by decide : 366018605 ≤ 366084141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 365953069 366084141).card = 457 := join_1_0

end S174C08
end Sude.GeneratedTwinScan
