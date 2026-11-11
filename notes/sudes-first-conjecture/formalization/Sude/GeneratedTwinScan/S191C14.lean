import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20060)) 402391085 402423853 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 402391085 402423853).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20060 402391085 402423853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20061)) 402423853 402456621 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 402423853 402456621).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20061 402423853 402456621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20062)) 402456621 402489389 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 402456621 402489389).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20062 402456621 402489389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20062)) 402489389 402522157 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 402489389 402522157).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20062 402489389 402522157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 402391085 402456621).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 402391085 ≤ 402423853)
    (by decide : 402423853 ≤ 402456621) block0 block1

theorem join_0_1 : (twinPrimeSegment 402456621 402522157).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 402456621 ≤ 402489389)
    (by decide : 402489389 ≤ 402522157) block2 block3

theorem join_1_0 : (twinPrimeSegment 402391085 402522157).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 402391085 ≤ 402456621)
    (by decide : 402456621 ≤ 402522157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 402391085 402522157).card = 467 := join_1_0

end S191C14
end Sude.GeneratedTwinScan
