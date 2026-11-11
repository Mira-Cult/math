import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22094)) 488112173 488144941 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 488112173 488144941).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22094 488112173 488144941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22094)) 488144941 488177709 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 488144941 488177709).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22094 488144941 488177709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22095)) 488177709 488210477 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 488177709 488210477).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22095 488177709 488210477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22096)) 488210477 488243245 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 488210477 488243245).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22096 488210477 488243245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 488112173 488177709).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 488112173 ≤ 488144941)
    (by decide : 488144941 ≤ 488177709) block0 block1

theorem join_0_1 : (twinPrimeSegment 488177709 488243245).card = 193 := by
  simpa using combineTwinPrimeSegments (by decide : 488177709 ≤ 488210477)
    (by decide : 488210477 ≤ 488243245) block2 block3

theorem join_1_0 : (twinPrimeSegment 488112173 488243245).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 488112173 ≤ 488177709)
    (by decide : 488177709 ≤ 488243245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 488112173 488243245).card = 424 := join_1_0

end S232C12
end Sude.GeneratedTwinScan
