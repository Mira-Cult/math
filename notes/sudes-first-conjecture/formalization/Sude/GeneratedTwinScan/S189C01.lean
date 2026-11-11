import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19912)) 396492845 396525613 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 396492845 396525613).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19912 396492845 396525613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19913)) 396525613 396558381 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 396525613 396558381).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19913 396525613 396558381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19914)) 396558381 396591149 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 396558381 396591149).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19914 396558381 396591149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19915)) 396591149 396623917 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 396591149 396623917).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19915 396591149 396623917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 396492845 396558381).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 396492845 ≤ 396525613)
    (by decide : 396525613 ≤ 396558381) block0 block1

theorem join_0_1 : (twinPrimeSegment 396558381 396623917).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 396558381 ≤ 396591149)
    (by decide : 396591149 ≤ 396623917) block2 block3

theorem join_1_0 : (twinPrimeSegment 396492845 396623917).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 396492845 ≤ 396558381)
    (by decide : 396558381 ≤ 396623917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 396492845 396623917).card = 460 := join_1_0

end S189C01
end Sude.GeneratedTwinScan
