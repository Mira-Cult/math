import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20851)) 434765869 434798637 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 434765869 434798637).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20851 434765869 434798637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20852)) 434798637 434831405 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 434798637 434831405).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20852 434798637 434831405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20853)) 434831405 434864173 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 434831405 434864173).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20853 434831405 434864173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20854)) 434864173 434896941 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 434864173 434896941).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20854 434864173 434896941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 434765869 434831405).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 434765869 ≤ 434798637)
    (by decide : 434798637 ≤ 434831405) block0 block1

theorem join_0_1 : (twinPrimeSegment 434831405 434896941).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 434831405 ≤ 434864173)
    (by decide : 434864173 ≤ 434896941) block2 block3

theorem join_1_0 : (twinPrimeSegment 434765869 434896941).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 434765869 ≤ 434831405)
    (by decide : 434831405 ≤ 434896941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 434765869 434896941).card = 435 := join_1_0

end S207C05
end Sude.GeneratedTwinScan
