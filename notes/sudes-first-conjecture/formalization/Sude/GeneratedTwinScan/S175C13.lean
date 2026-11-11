import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19202)) 368705581 368738349 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 368705581 368738349).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19202 368705581 368738349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19203)) 368738349 368771117 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 368738349 368771117).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19203 368738349 368771117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19204)) 368771117 368803885 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 368771117 368803885).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19204 368771117 368803885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19205)) 368803885 368836653 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 368803885 368836653).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19205 368803885 368836653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 368705581 368771117).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 368705581 ≤ 368738349)
    (by decide : 368738349 ≤ 368771117) block0 block1

theorem join_0_1 : (twinPrimeSegment 368771117 368836653).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 368771117 ≤ 368803885)
    (by decide : 368803885 ≤ 368836653) block2 block3

theorem join_1_0 : (twinPrimeSegment 368705581 368836653).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 368705581 ≤ 368771117)
    (by decide : 368771117 ≤ 368836653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 368705581 368836653).card = 427 := join_1_0

end S175C13
end Sude.GeneratedTwinScan
