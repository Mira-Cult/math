import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16524)) 273023021 273055789 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 273023021 273055789).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16524 273023021 273055789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16525)) 273055789 273088557 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 273055789 273088557).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16525 273055789 273088557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16526)) 273088557 273121325 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 273088557 273121325).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16526 273088557 273121325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16527)) 273121325 273154093 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 273121325 273154093).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16527 273121325 273154093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 273023021 273088557).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 273023021 ≤ 273055789)
    (by decide : 273055789 ≤ 273088557) block0 block1

theorem join_0_1 : (twinPrimeSegment 273088557 273154093).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 273088557 ≤ 273121325)
    (by decide : 273121325 ≤ 273154093) block2 block3

theorem join_1_0 : (twinPrimeSegment 273023021 273154093).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 273023021 ≤ 273088557)
    (by decide : 273088557 ≤ 273154093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 273023021 273154093).card = 452 := join_1_0

end S130C03
end Sude.GeneratedTwinScan
