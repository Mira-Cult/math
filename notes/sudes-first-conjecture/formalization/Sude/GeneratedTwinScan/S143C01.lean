import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17322)) 300023853 300056621 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 300023853 300056621).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17322 300023853 300056621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17323)) 300056621 300089389 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 300056621 300089389).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17323 300056621 300089389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17324)) 300089389 300122157 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 300089389 300122157).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17324 300089389 300122157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17324)) 300122157 300154925 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 300122157 300154925).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17324 300122157 300154925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 300023853 300089389).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 300023853 ≤ 300056621)
    (by decide : 300056621 ≤ 300089389) block0 block1

theorem join_0_1 : (twinPrimeSegment 300089389 300154925).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 300089389 ≤ 300122157)
    (by decide : 300122157 ≤ 300154925) block2 block3

theorem join_1_0 : (twinPrimeSegment 300023853 300154925).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 300023853 ≤ 300089389)
    (by decide : 300089389 ≤ 300154925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 300023853 300154925).card = 420 := join_1_0

end S143C01
end Sude.GeneratedTwinScan
