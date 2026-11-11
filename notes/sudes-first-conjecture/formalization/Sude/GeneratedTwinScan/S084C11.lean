import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13327)) 177602605 177635373 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 177602605 177635373).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13327 177602605 177635373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13329)) 177635373 177668141 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 177635373 177668141).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13329 177635373 177668141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13330)) 177668141 177700909 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 177668141 177700909).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13330 177668141 177700909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13331)) 177700909 177733677 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 177700909 177733677).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13331 177700909 177733677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 177602605 177668141).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 177602605 ≤ 177635373)
    (by decide : 177635373 ≤ 177668141) block0 block1

theorem join_0_1 : (twinPrimeSegment 177668141 177733677).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 177668141 ≤ 177700909)
    (by decide : 177700909 ≤ 177733677) block2 block3

theorem join_1_0 : (twinPrimeSegment 177602605 177733677).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 177602605 ≤ 177668141)
    (by decide : 177668141 ≤ 177733677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 177602605 177733677).card = 444 := join_1_0

end S084C11
end Sude.GeneratedTwinScan
