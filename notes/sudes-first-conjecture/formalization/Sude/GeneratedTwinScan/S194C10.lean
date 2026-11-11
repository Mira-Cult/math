import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20203)) 408158253 408191021 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 408158253 408191021).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20203 408158253 408191021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20204)) 408191021 408223789 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 408191021 408223789).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20204 408191021 408223789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20205)) 408223789 408256557 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 408223789 408256557).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20205 408223789 408256557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20206)) 408256557 408289325 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 408256557 408289325).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20206 408256557 408289325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 408158253 408223789).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 408158253 ≤ 408191021)
    (by decide : 408191021 ≤ 408223789) block0 block1

theorem join_0_1 : (twinPrimeSegment 408223789 408289325).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 408223789 ≤ 408256557)
    (by decide : 408256557 ≤ 408289325) block2 block3

theorem join_1_0 : (twinPrimeSegment 408158253 408289325).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 408158253 ≤ 408223789)
    (by decide : 408223789 ≤ 408289325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 408158253 408289325).card = 441 := join_1_0

end S194C10
end Sude.GeneratedTwinScan
