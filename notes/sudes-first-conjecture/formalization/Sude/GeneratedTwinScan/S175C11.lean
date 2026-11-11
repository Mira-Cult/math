import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19195)) 368443437 368476205 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 368443437 368476205).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19195 368443437 368476205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19196)) 368476205 368508973 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 368476205 368508973).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19196 368476205 368508973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19197)) 368508973 368541741 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 368508973 368541741).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19197 368508973 368541741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19198)) 368541741 368574509 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 368541741 368574509).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19198 368541741 368574509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 368443437 368508973).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 368443437 ≤ 368476205)
    (by decide : 368476205 ≤ 368508973) block0 block1

theorem join_0_1 : (twinPrimeSegment 368508973 368574509).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 368508973 ≤ 368541741)
    (by decide : 368541741 ≤ 368574509) block2 block3

theorem join_1_0 : (twinPrimeSegment 368443437 368574509).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 368443437 ≤ 368508973)
    (by decide : 368508973 ≤ 368574509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 368443437 368574509).card = 425 := join_1_0

end S175C11
end Sude.GeneratedTwinScan
