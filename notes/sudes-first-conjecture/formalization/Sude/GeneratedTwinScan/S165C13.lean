import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18648)) 347734061 347766829 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 347734061 347766829).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18648 347734061 347766829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18649)) 347766829 347799597 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 347766829 347799597).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18649 347766829 347799597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18650)) 347799597 347832365 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 347799597 347832365).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18650 347799597 347832365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18651)) 347832365 347865133 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 347832365 347865133).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18651 347832365 347865133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 347734061 347799597).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 347734061 ≤ 347766829)
    (by decide : 347766829 ≤ 347799597) block0 block1

theorem join_0_1 : (twinPrimeSegment 347799597 347865133).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 347799597 ≤ 347832365)
    (by decide : 347832365 ≤ 347865133) block2 block3

theorem join_1_0 : (twinPrimeSegment 347734061 347865133).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 347734061 ≤ 347799597)
    (by decide : 347799597 ≤ 347865133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 347734061 347865133).card = 460 := join_1_0

end S165C13
end Sude.GeneratedTwinScan
