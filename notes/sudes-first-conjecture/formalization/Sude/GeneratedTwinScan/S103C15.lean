import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14765)) 217972781 218005549 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 217972781 218005549).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14765 217972781 218005549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14766)) 218005549 218038317 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 218005549 218038317).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14766 218005549 218038317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14767)) 218038317 218071085 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 218038317 218071085).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14767 218038317 218071085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14768)) 218071085 218103853 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 218071085 218103853).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14768 218071085 218103853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 217972781 218038317).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 217972781 ≤ 218005549)
    (by decide : 218005549 ≤ 218038317) block0 block1

theorem join_0_1 : (twinPrimeSegment 218038317 218103853).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 218038317 ≤ 218071085)
    (by decide : 218071085 ≤ 218103853) block2 block3

theorem join_1_0 : (twinPrimeSegment 217972781 218103853).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 217972781 ≤ 218038317)
    (by decide : 218038317 ≤ 218103853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 217972781 218103853).card = 471 := join_1_0

end S103C15
end Sude.GeneratedTwinScan
