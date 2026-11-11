import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19372)) 375259181 375291949 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 375259181 375291949).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19372 375259181 375291949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19373)) 375291949 375324717 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 375291949 375324717).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19373 375291949 375324717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19374)) 375324717 375357485 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 375324717 375357485).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19374 375324717 375357485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19374)) 375357485 375390253 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 375357485 375390253).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19374 375357485 375390253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 375259181 375324717).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 375259181 ≤ 375291949)
    (by decide : 375291949 ≤ 375324717) block0 block1

theorem join_0_1 : (twinPrimeSegment 375324717 375390253).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 375324717 ≤ 375357485)
    (by decide : 375357485 ≤ 375390253) block2 block3

theorem join_1_0 : (twinPrimeSegment 375259181 375390253).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 375259181 ≤ 375324717)
    (by decide : 375324717 ≤ 375390253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 375259181 375390253).card = 429 := join_1_0

end S178C15
end Sude.GeneratedTwinScan
