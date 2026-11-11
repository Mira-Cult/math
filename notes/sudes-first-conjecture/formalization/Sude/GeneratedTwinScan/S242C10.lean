import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22557)) 508821549 508854317 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 508821549 508854317).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22557 508821549 508854317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22558)) 508854317 508887085 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 508854317 508887085).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22558 508854317 508887085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22559)) 508887085 508919853 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 508887085 508919853).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22559 508887085 508919853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22559)) 508919853 508952621 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 508919853 508952621).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22559 508919853 508952621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 508821549 508887085).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 508821549 ≤ 508854317)
    (by decide : 508854317 ≤ 508887085) block0 block1

theorem join_0_1 : (twinPrimeSegment 508887085 508952621).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 508887085 ≤ 508919853)
    (by decide : 508919853 ≤ 508952621) block2 block3

theorem join_1_0 : (twinPrimeSegment 508821549 508952621).card = 408 := by
  simpa using combineTwinPrimeSegments (by decide : 508821549 ≤ 508887085)
    (by decide : 508887085 ≤ 508952621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 508821549 508952621).card = 408 := join_1_0

end S242C10
end Sude.GeneratedTwinScan
