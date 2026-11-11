import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21194)) 449183789 449216557 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 449183789 449216557).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21194 449183789 449216557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21195)) 449216557 449249325 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 449216557 449249325).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21195 449216557 449249325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21196)) 449249325 449282093 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 449249325 449282093).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21196 449249325 449282093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21197)) 449282093 449314861 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 449282093 449314861).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21197 449282093 449314861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 449183789 449249325).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 449183789 ≤ 449216557)
    (by decide : 449216557 ≤ 449249325) block0 block1

theorem join_0_1 : (twinPrimeSegment 449249325 449314861).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 449249325 ≤ 449282093)
    (by decide : 449282093 ≤ 449314861) block2 block3

theorem join_1_0 : (twinPrimeSegment 449183789 449314861).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 449183789 ≤ 449249325)
    (by decide : 449249325 ≤ 449314861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 449183789 449314861).card = 439 := join_1_0

end S214C03
end Sude.GeneratedTwinScan
