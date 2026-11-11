import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17625)) 310640685 310673453 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 310640685 310673453).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17625 310640685 310673453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17626)) 310673453 310706221 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 310673453 310706221).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17626 310673453 310706221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17627)) 310706221 310738989 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 310706221 310738989).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17627 310706221 310738989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17628)) 310738989 310771757 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 310738989 310771757).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17628 310738989 310771757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 310640685 310706221).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 310640685 ≤ 310673453)
    (by decide : 310673453 ≤ 310706221) block0 block1

theorem join_0_1 : (twinPrimeSegment 310706221 310771757).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 310706221 ≤ 310738989)
    (by decide : 310738989 ≤ 310771757) block2 block3

theorem join_1_0 : (twinPrimeSegment 310640685 310771757).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 310640685 ≤ 310706221)
    (by decide : 310706221 ≤ 310771757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 310640685 310771757).card = 431 := join_1_0

end S148C02
end Sude.GeneratedTwinScan
