import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15773)) 248774701 248807469 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 248774701 248807469).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15773 248774701 248807469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15774)) 248807469 248840237 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 248807469 248840237).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15774 248807469 248840237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15775)) 248840237 248873005 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 248840237 248873005).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15775 248840237 248873005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15776)) 248873005 248905773 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 248873005 248905773).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15776 248873005 248905773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 248774701 248840237).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 248774701 ≤ 248807469)
    (by decide : 248807469 ≤ 248840237) block0 block1

theorem join_0_1 : (twinPrimeSegment 248840237 248905773).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 248840237 ≤ 248873005)
    (by decide : 248873005 ≤ 248905773) block2 block3

theorem join_1_0 : (twinPrimeSegment 248774701 248905773).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 248774701 ≤ 248840237)
    (by decide : 248840237 ≤ 248905773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 248774701 248905773).card = 444 := join_1_0

end S118C10
end Sude.GeneratedTwinScan
