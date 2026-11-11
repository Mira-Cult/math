import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20630)) 425590829 425623597 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 425590829 425623597).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20630 425590829 425623597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20631)) 425623597 425656365 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 425623597 425656365).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20631 425623597 425656365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20632)) 425656365 425689133 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 425656365 425689133).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20632 425656365 425689133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20633)) 425689133 425721901 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 425689133 425721901).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20633 425689133 425721901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 425590829 425656365).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 425590829 ≤ 425623597)
    (by decide : 425623597 ≤ 425656365) block0 block1

theorem join_0_1 : (twinPrimeSegment 425656365 425721901).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 425656365 ≤ 425689133)
    (by decide : 425689133 ≤ 425721901) block2 block3

theorem join_1_0 : (twinPrimeSegment 425590829 425721901).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 425590829 ≤ 425656365)
    (by decide : 425656365 ≤ 425721901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 425590829 425721901).card = 443 := join_1_0

end S202C15
end Sude.GeneratedTwinScan
