import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15623)) 244056109 244088877 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 244056109 244088877).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15623 244056109 244088877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15624)) 244088877 244121645 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 244088877 244121645).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15624 244088877 244121645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15625)) 244121645 244154413 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 244121645 244154413).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15625 244121645 244154413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15626)) 244154413 244187181 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 244154413 244187181).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15626 244154413 244187181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 244056109 244121645).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 244056109 ≤ 244088877)
    (by decide : 244088877 ≤ 244121645) block0 block1

theorem join_0_1 : (twinPrimeSegment 244121645 244187181).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 244121645 ≤ 244154413)
    (by decide : 244154413 ≤ 244187181) block2 block3

theorem join_1_0 : (twinPrimeSegment 244056109 244187181).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 244056109 ≤ 244121645)
    (by decide : 244121645 ≤ 244187181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 244056109 244187181).card = 467 := join_1_0

end S116C06
end Sude.GeneratedTwinScan
