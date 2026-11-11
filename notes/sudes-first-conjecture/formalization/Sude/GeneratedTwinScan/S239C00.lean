import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22388)) 501219373 501252141 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 501219373 501252141).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22388 501219373 501252141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22389)) 501252141 501284909 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 501252141 501284909).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22389 501252141 501284909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22390)) 501284909 501317677 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 501284909 501317677).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22390 501284909 501317677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22390)) 501317677 501350445 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 501317677 501350445).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22390 501317677 501350445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 501219373 501284909).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 501219373 ≤ 501252141)
    (by decide : 501252141 ≤ 501284909) block0 block1

theorem join_0_1 : (twinPrimeSegment 501284909 501350445).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 501284909 ≤ 501317677)
    (by decide : 501317677 ≤ 501350445) block2 block3

theorem join_1_0 : (twinPrimeSegment 501219373 501350445).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 501219373 ≤ 501284909)
    (by decide : 501284909 ≤ 501350445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 501219373 501350445).card = 416 := join_1_0

end S239C00
end Sude.GeneratedTwinScan
