import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15450)) 238682157 238714925 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 238682157 238714925).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15450 238682157 238714925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15451)) 238714925 238747693 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 238714925 238747693).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15451 238714925 238747693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15452)) 238747693 238780461 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 238747693 238780461).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15452 238747693 238780461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15453)) 238780461 238813229 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 238780461 238813229).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15453 238780461 238813229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 238682157 238747693).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 238682157 ≤ 238714925)
    (by decide : 238714925 ≤ 238747693) block0 block1

theorem join_0_1 : (twinPrimeSegment 238747693 238813229).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 238747693 ≤ 238780461)
    (by decide : 238780461 ≤ 238813229) block2 block3

theorem join_1_0 : (twinPrimeSegment 238682157 238813229).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 238682157 ≤ 238747693)
    (by decide : 238747693 ≤ 238813229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 238682157 238813229).card = 456 := join_1_0

end S113C13
end Sude.GeneratedTwinScan
