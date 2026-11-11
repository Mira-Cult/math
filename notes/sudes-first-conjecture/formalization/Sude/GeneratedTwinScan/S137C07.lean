import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16978)) 288227373 288260141 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 288227373 288260141).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16978 288227373 288260141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16979)) 288260141 288292909 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 288260141 288292909).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16979 288260141 288292909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16980)) 288292909 288325677 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 288292909 288325677).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16980 288292909 288325677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16981)) 288325677 288358445 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 288325677 288358445).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16981 288325677 288358445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 288227373 288292909).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 288227373 ≤ 288260141)
    (by decide : 288260141 ≤ 288292909) block0 block1

theorem join_0_1 : (twinPrimeSegment 288292909 288358445).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 288292909 ≤ 288325677)
    (by decide : 288325677 ≤ 288358445) block2 block3

theorem join_1_0 : (twinPrimeSegment 288227373 288358445).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 288227373 ≤ 288292909)
    (by decide : 288292909 ≤ 288358445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 288227373 288358445).card = 480 := join_1_0

end S137C07
end Sude.GeneratedTwinScan
