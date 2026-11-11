import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12984)) 168558637 168591405 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 168558637 168591405).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12984 168558637 168591405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12985)) 168591405 168624173 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 168591405 168624173).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12985 168591405 168624173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12986)) 168624173 168656941 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 168624173 168656941).card = 142 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12986 168624173 168656941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12988)) 168656941 168689709 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 168656941 168689709).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12988 168656941 168689709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 168558637 168624173).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 168558637 ≤ 168591405)
    (by decide : 168591405 ≤ 168624173) block0 block1

theorem join_0_1 : (twinPrimeSegment 168624173 168689709).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 168624173 ≤ 168656941)
    (by decide : 168656941 ≤ 168689709) block2 block3

theorem join_1_0 : (twinPrimeSegment 168558637 168689709).card = 503 := by
  simpa using combineTwinPrimeSegments (by decide : 168558637 ≤ 168624173)
    (by decide : 168624173 ≤ 168689709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 168558637 168689709).card = 503 := join_1_0

end S080C06
end Sude.GeneratedTwinScan
