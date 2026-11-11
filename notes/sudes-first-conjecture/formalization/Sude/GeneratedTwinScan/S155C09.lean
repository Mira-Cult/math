import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18062)) 326238253 326271021 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 326238253 326271021).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18062 326238253 326271021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18063)) 326271021 326303789 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 326271021 326303789).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18063 326271021 326303789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18064)) 326303789 326336557 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 326303789 326336557).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18064 326303789 326336557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18065)) 326336557 326369325 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 326336557 326369325).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18065 326336557 326369325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 326238253 326303789).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 326238253 ≤ 326271021)
    (by decide : 326271021 ≤ 326303789) block0 block1

theorem join_0_1 : (twinPrimeSegment 326303789 326369325).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 326303789 ≤ 326336557)
    (by decide : 326336557 ≤ 326369325) block2 block3

theorem join_1_0 : (twinPrimeSegment 326238253 326369325).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 326238253 ≤ 326303789)
    (by decide : 326303789 ≤ 326369325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 326238253 326369325).card = 447 := join_1_0

end S155C09
end Sude.GeneratedTwinScan
