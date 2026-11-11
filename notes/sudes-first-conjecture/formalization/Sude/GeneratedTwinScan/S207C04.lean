import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20848)) 434634797 434667565 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 434634797 434667565).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20848 434634797 434667565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20849)) 434667565 434700333 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 434667565 434700333).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20849 434667565 434700333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20850)) 434700333 434733101 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 434700333 434733101).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20850 434700333 434733101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20851)) 434733101 434765869 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 434733101 434765869).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20851 434733101 434765869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 434634797 434700333).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 434634797 ≤ 434667565)
    (by decide : 434667565 ≤ 434700333) block0 block1

theorem join_0_1 : (twinPrimeSegment 434700333 434765869).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 434700333 ≤ 434733101)
    (by decide : 434733101 ≤ 434765869) block2 block3

theorem join_1_0 : (twinPrimeSegment 434634797 434765869).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 434634797 ≤ 434700333)
    (by decide : 434700333 ≤ 434765869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 434634797 434765869).card = 442 := join_1_0

end S207C04
end Sude.GeneratedTwinScan
