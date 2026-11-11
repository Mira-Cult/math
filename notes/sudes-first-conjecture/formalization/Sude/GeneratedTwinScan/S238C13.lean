import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22379)) 500826157 500858925 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 500826157 500858925).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22379 500826157 500858925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22380)) 500858925 500891693 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 500858925 500891693).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22380 500858925 500891693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22381)) 500891693 500924461 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 500891693 500924461).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22381 500891693 500924461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22382)) 500924461 500957229 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 500924461 500957229).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22382 500924461 500957229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 500826157 500891693).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 500826157 ≤ 500858925)
    (by decide : 500858925 ≤ 500891693) block0 block1

theorem join_0_1 : (twinPrimeSegment 500891693 500957229).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 500891693 ≤ 500924461)
    (by decide : 500924461 ≤ 500957229) block2 block3

theorem join_1_0 : (twinPrimeSegment 500826157 500957229).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 500826157 ≤ 500891693)
    (by decide : 500891693 ≤ 500957229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 500826157 500957229).card = 456 := join_1_0

end S238C13
end Sude.GeneratedTwinScan
