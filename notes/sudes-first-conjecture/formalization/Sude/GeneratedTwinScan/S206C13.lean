import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20826)) 433717293 433750061 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 433717293 433750061).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20826 433717293 433750061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20827)) 433750061 433782829 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 433750061 433782829).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20827 433750061 433782829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20828)) 433782829 433815597 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 433782829 433815597).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20828 433782829 433815597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20829)) 433815597 433848365 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 433815597 433848365).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20829 433815597 433848365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 433717293 433782829).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 433717293 ≤ 433750061)
    (by decide : 433750061 ≤ 433782829) block0 block1

theorem join_0_1 : (twinPrimeSegment 433782829 433848365).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 433782829 ≤ 433815597)
    (by decide : 433815597 ≤ 433848365) block2 block3

theorem join_1_0 : (twinPrimeSegment 433717293 433848365).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 433717293 ≤ 433782829)
    (by decide : 433782829 ≤ 433848365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 433717293 433848365).card = 444 := join_1_0

end S206C13
end Sude.GeneratedTwinScan
