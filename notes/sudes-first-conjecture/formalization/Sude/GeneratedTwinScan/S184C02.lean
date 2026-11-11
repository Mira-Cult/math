import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19651)) 386138157 386170925 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 386138157 386170925).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19651 386138157 386170925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19652)) 386170925 386203693 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 386170925 386203693).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19652 386170925 386203693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19652)) 386203693 386236461 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 386203693 386236461).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19652 386203693 386236461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19653)) 386236461 386269229 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 386236461 386269229).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19653 386236461 386269229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 386138157 386203693).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 386138157 ≤ 386170925)
    (by decide : 386170925 ≤ 386203693) block0 block1

theorem join_0_1 : (twinPrimeSegment 386203693 386269229).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 386203693 ≤ 386236461)
    (by decide : 386236461 ≤ 386269229) block2 block3

theorem join_1_0 : (twinPrimeSegment 386138157 386269229).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 386138157 ≤ 386203693)
    (by decide : 386203693 ≤ 386269229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 386138157 386269229).card = 444 := join_1_0

end S184C02
end Sude.GeneratedTwinScan
