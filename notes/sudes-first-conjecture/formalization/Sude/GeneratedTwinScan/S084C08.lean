import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13313)) 177209389 177242157 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 177209389 177242157).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13313 177209389 177242157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13314)) 177242157 177274925 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 177242157 177274925).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13314 177242157 177274925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13315)) 177274925 177307693 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 177274925 177307693).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13315 177274925 177307693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13316)) 177307693 177340461 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 177307693 177340461).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13316 177307693 177340461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 177209389 177274925).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 177209389 ≤ 177242157)
    (by decide : 177242157 ≤ 177274925) block0 block1

theorem join_0_1 : (twinPrimeSegment 177274925 177340461).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 177274925 ≤ 177307693)
    (by decide : 177307693 ≤ 177340461) block2 block3

theorem join_1_0 : (twinPrimeSegment 177209389 177340461).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 177209389 ≤ 177274925)
    (by decide : 177274925 ≤ 177340461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 177209389 177340461).card = 486 := join_1_0

end S084C08
end Sude.GeneratedTwinScan
