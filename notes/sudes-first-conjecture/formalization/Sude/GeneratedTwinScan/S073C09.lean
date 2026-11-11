import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12421)) 154271789 154304557 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 154271789 154304557).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12421 154271789 154304557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12423)) 154304557 154337325 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 154304557 154337325).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12423 154304557 154337325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12424)) 154337325 154370093 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 154337325 154370093).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12424 154337325 154370093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12425)) 154370093 154402861 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 154370093 154402861).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12425 154370093 154402861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 154271789 154337325).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 154271789 ≤ 154304557)
    (by decide : 154304557 ≤ 154337325) block0 block1

theorem join_0_1 : (twinPrimeSegment 154337325 154402861).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 154337325 ≤ 154370093)
    (by decide : 154370093 ≤ 154402861) block2 block3

theorem join_1_0 : (twinPrimeSegment 154271789 154402861).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 154271789 ≤ 154337325)
    (by decide : 154337325 ≤ 154402861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 154271789 154402861).card = 501 := join_1_0

end S073C09
end Sude.GeneratedTwinScan
