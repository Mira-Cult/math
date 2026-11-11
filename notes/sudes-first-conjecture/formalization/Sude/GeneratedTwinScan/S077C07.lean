import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12744)) 162398253 162431021 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 162398253 162431021).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12744 162398253 162431021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12746)) 162431021 162463789 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 162431021 162463789).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12746 162431021 162463789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12747)) 162463789 162496557 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 162463789 162496557).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12747 162463789 162496557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12748)) 162496557 162529325 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 162496557 162529325).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12748 162496557 162529325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 162398253 162463789).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 162398253 ≤ 162431021)
    (by decide : 162431021 ≤ 162463789) block0 block1

theorem join_0_1 : (twinPrimeSegment 162463789 162529325).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 162463789 ≤ 162496557)
    (by decide : 162496557 ≤ 162529325) block2 block3

theorem join_1_0 : (twinPrimeSegment 162398253 162529325).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 162398253 ≤ 162463789)
    (by decide : 162463789 ≤ 162529325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 162398253 162529325).card = 468 := join_1_0

end S077C07
end Sude.GeneratedTwinScan
