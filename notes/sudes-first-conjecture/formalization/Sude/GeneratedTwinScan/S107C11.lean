import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15028)) 225837101 225869869 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 225837101 225869869).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15028 225837101 225869869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15030)) 225869869 225902637 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 225869869 225902637).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15030 225869869 225902637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15031)) 225902637 225935405 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 225902637 225935405).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15031 225902637 225935405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15032)) 225935405 225968173 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 225935405 225968173).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15032 225935405 225968173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 225837101 225902637).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 225837101 ≤ 225869869)
    (by decide : 225869869 ≤ 225902637) block0 block1

theorem join_0_1 : (twinPrimeSegment 225902637 225968173).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 225902637 ≤ 225935405)
    (by decide : 225935405 ≤ 225968173) block2 block3

theorem join_1_0 : (twinPrimeSegment 225837101 225968173).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 225837101 ≤ 225902637)
    (by decide : 225902637 ≤ 225968173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 225837101 225968173).card = 480 := join_1_0

end S107C11
end Sude.GeneratedTwinScan
