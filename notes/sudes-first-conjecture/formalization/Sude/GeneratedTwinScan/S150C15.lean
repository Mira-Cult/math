import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17792)) 316538925 316571693 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 316538925 316571693).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17792 316538925 316571693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17793)) 316571693 316604461 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 316571693 316604461).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17793 316571693 316604461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17794)) 316604461 316637229 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 316604461 316637229).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17794 316604461 316637229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17795)) 316637229 316669997 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 316637229 316669997).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17795 316637229 316669997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 316538925 316604461).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 316538925 ≤ 316571693)
    (by decide : 316571693 ≤ 316604461) block0 block1

theorem join_0_1 : (twinPrimeSegment 316604461 316669997).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 316604461 ≤ 316637229)
    (by decide : 316637229 ≤ 316669997) block2 block3

theorem join_1_0 : (twinPrimeSegment 316538925 316669997).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 316538925 ≤ 316604461)
    (by decide : 316604461 ≤ 316669997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 316538925 316669997).card = 445 := join_1_0

end S150C15
end Sude.GeneratedTwinScan
