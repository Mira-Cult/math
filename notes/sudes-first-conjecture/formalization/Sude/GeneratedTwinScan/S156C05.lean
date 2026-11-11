import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18106)) 327811117 327843885 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 327811117 327843885).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18106 327811117 327843885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18107)) 327843885 327876653 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 327843885 327876653).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18107 327843885 327876653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18108)) 327876653 327909421 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 327876653 327909421).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18108 327876653 327909421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18109)) 327909421 327942189 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 327909421 327942189).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18109 327909421 327942189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 327811117 327876653).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 327811117 ≤ 327843885)
    (by decide : 327843885 ≤ 327876653) block0 block1

theorem join_0_1 : (twinPrimeSegment 327876653 327942189).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 327876653 ≤ 327909421)
    (by decide : 327909421 ≤ 327942189) block2 block3

theorem join_1_0 : (twinPrimeSegment 327811117 327942189).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 327811117 ≤ 327876653)
    (by decide : 327876653 ≤ 327942189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 327811117 327942189).card = 460 := join_1_0

end S156C05
end Sude.GeneratedTwinScan
