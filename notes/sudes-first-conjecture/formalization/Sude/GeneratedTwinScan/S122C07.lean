import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16025)) 256770093 256802861 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 256770093 256802861).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16025 256770093 256802861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16026)) 256802861 256835629 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 256802861 256835629).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16026 256802861 256835629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16027)) 256835629 256868397 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 256835629 256868397).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16027 256835629 256868397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16028)) 256868397 256901165 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 256868397 256901165).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16028 256868397 256901165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 256770093 256835629).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 256770093 ≤ 256802861)
    (by decide : 256802861 ≤ 256835629) block0 block1

theorem join_0_1 : (twinPrimeSegment 256835629 256901165).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 256835629 ≤ 256868397)
    (by decide : 256868397 ≤ 256901165) block2 block3

theorem join_1_0 : (twinPrimeSegment 256770093 256901165).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 256770093 ≤ 256835629)
    (by decide : 256835629 ≤ 256901165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 256770093 256901165).card = 444 := join_1_0

end S122C07
end Sude.GeneratedTwinScan
