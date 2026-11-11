import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16811)) 282591277 282624045 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 282591277 282624045).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16811 282591277 282624045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16812)) 282624045 282656813 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 282624045 282656813).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16812 282624045 282656813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16813)) 282656813 282689581 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 282656813 282689581).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16813 282656813 282689581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16814)) 282689581 282722349 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 282689581 282722349).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16814 282689581 282722349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 282591277 282656813).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 282591277 ≤ 282624045)
    (by decide : 282624045 ≤ 282656813) block0 block1

theorem join_0_1 : (twinPrimeSegment 282656813 282722349).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 282656813 ≤ 282689581)
    (by decide : 282689581 ≤ 282722349) block2 block3

theorem join_1_0 : (twinPrimeSegment 282591277 282722349).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 282591277 ≤ 282656813)
    (by decide : 282656813 ≤ 282722349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 282591277 282722349).card = 450 := join_1_0

end S134C12
end Sude.GeneratedTwinScan
