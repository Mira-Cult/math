import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17154)) 294256685 294289453 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 294256685 294289453).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17154 294256685 294289453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17155)) 294289453 294322221 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 294289453 294322221).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17155 294289453 294322221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17156)) 294322221 294354989 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 294322221 294354989).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17156 294322221 294354989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17157)) 294354989 294387757 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 294354989 294387757).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17157 294354989 294387757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 294256685 294322221).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 294256685 ≤ 294289453)
    (by decide : 294289453 ≤ 294322221) block0 block1

theorem join_0_1 : (twinPrimeSegment 294322221 294387757).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 294322221 ≤ 294354989)
    (by decide : 294354989 ≤ 294387757) block2 block3

theorem join_1_0 : (twinPrimeSegment 294256685 294387757).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 294256685 ≤ 294322221)
    (by decide : 294322221 ≤ 294387757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 294256685 294387757).card = 494 := join_1_0

end S140C05
end Sude.GeneratedTwinScan
