import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17674)) 312344621 312377389 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 312344621 312377389).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17674 312344621 312377389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17675)) 312377389 312410157 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 312377389 312410157).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17675 312377389 312410157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17676)) 312410157 312442925 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 312410157 312442925).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17676 312410157 312442925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17676)) 312442925 312475693 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 312442925 312475693).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17676 312442925 312475693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 312344621 312410157).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 312344621 ≤ 312377389)
    (by decide : 312377389 ≤ 312410157) block0 block1

theorem join_0_1 : (twinPrimeSegment 312410157 312475693).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 312410157 ≤ 312442925)
    (by decide : 312442925 ≤ 312475693) block2 block3

theorem join_1_0 : (twinPrimeSegment 312344621 312475693).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 312344621 ≤ 312410157)
    (by decide : 312410157 ≤ 312475693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 312344621 312475693).card = 465 := join_1_0

end S148C15
end Sude.GeneratedTwinScan
