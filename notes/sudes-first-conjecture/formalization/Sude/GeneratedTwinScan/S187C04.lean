import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19817)) 392691757 392724525 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 392691757 392724525).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19817 392691757 392724525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19818)) 392724525 392757293 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 392724525 392757293).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19818 392724525 392757293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19818)) 392757293 392790061 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 392757293 392790061).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19818 392757293 392790061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19819)) 392790061 392822829 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 392790061 392822829).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19819 392790061 392822829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 392691757 392757293).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 392691757 ≤ 392724525)
    (by decide : 392724525 ≤ 392757293) block0 block1

theorem join_0_1 : (twinPrimeSegment 392757293 392822829).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 392757293 ≤ 392790061)
    (by decide : 392790061 ≤ 392822829) block2 block3

theorem join_1_0 : (twinPrimeSegment 392691757 392822829).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 392691757 ≤ 392757293)
    (by decide : 392757293 ≤ 392822829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 392691757 392822829).card = 429 := join_1_0

end S187C04
end Sude.GeneratedTwinScan
