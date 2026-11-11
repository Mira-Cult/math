import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20735)) 429916205 429948973 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 429916205 429948973).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20735 429916205 429948973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20736)) 429948973 429981741 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 429948973 429981741).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20736 429948973 429981741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20736)) 429981741 430014509 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 429981741 430014509).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20736 429981741 430014509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20737)) 430014509 430047277 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 430014509 430047277).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20737 430014509 430047277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 429916205 429981741).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 429916205 ≤ 429948973)
    (by decide : 429948973 ≤ 429981741) block0 block1

theorem join_0_1 : (twinPrimeSegment 429981741 430047277).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 429981741 ≤ 430014509)
    (by decide : 430014509 ≤ 430047277) block2 block3

theorem join_1_0 : (twinPrimeSegment 429916205 430047277).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 429916205 ≤ 429981741)
    (by decide : 429981741 ≤ 430047277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 429916205 430047277).card = 463 := join_1_0

end S205C00
end Sude.GeneratedTwinScan
