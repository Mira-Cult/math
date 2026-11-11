import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18182)) 330563629 330596397 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 330563629 330596397).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18182 330563629 330596397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18183)) 330596397 330629165 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 330596397 330629165).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18183 330596397 330629165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18184)) 330629165 330661933 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 330629165 330661933).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18184 330629165 330661933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18185)) 330661933 330694701 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 330661933 330694701).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18185 330661933 330694701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 330563629 330629165).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 330563629 ≤ 330596397)
    (by decide : 330596397 ≤ 330629165) block0 block1

theorem join_0_1 : (twinPrimeSegment 330629165 330694701).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 330629165 ≤ 330661933)
    (by decide : 330661933 ≤ 330694701) block2 block3

theorem join_1_0 : (twinPrimeSegment 330563629 330694701).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 330563629 ≤ 330629165)
    (by decide : 330629165 ≤ 330694701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 330563629 330694701).card = 463 := join_1_0

end S157C10
end Sude.GeneratedTwinScan
