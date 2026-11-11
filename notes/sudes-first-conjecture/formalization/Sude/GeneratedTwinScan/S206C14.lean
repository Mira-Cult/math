import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20829)) 433848365 433881133 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 433848365 433881133).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20829 433848365 433881133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20830)) 433881133 433913901 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 433881133 433913901).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20830 433881133 433913901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20831)) 433913901 433946669 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 433913901 433946669).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20831 433913901 433946669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20832)) 433946669 433979437 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 433946669 433979437).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20832 433946669 433979437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 433848365 433913901).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 433848365 ≤ 433881133)
    (by decide : 433881133 ≤ 433913901) block0 block1

theorem join_0_1 : (twinPrimeSegment 433913901 433979437).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 433913901 ≤ 433946669)
    (by decide : 433946669 ≤ 433979437) block2 block3

theorem join_1_0 : (twinPrimeSegment 433848365 433979437).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 433848365 ≤ 433913901)
    (by decide : 433913901 ≤ 433979437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 433848365 433979437).card = 449 := join_1_0

end S206C14
end Sude.GeneratedTwinScan
