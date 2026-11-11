import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21804)) 475398189 475430957 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 475398189 475430957).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21804 475398189 475430957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21805)) 475430957 475463725 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 475430957 475463725).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21805 475430957 475463725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21805)) 475463725 475496493 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 475463725 475496493).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21805 475463725 475496493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21806)) 475496493 475529261 = 88 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 475496493 475529261).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21806 475496493 475529261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 475398189 475463725).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 475398189 ≤ 475430957)
    (by decide : 475430957 ≤ 475463725) block0 block1

theorem join_0_1 : (twinPrimeSegment 475463725 475529261).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 475463725 ≤ 475496493)
    (by decide : 475496493 ≤ 475529261) block2 block3

theorem join_1_0 : (twinPrimeSegment 475398189 475529261).card = 406 := by
  simpa using combineTwinPrimeSegments (by decide : 475398189 ≤ 475463725)
    (by decide : 475463725 ≤ 475529261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 475398189 475529261).card = 406 := join_1_0

end S226C11
end Sude.GeneratedTwinScan
