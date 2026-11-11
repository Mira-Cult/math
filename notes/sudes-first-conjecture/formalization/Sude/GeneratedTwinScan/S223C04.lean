import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21638)) 468189229 468221997 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 468189229 468221997).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21638 468189229 468221997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21639)) 468221997 468254765 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 468221997 468254765).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21639 468221997 468254765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21639)) 468254765 468287533 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 468254765 468287533).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21639 468254765 468287533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21640)) 468287533 468320301 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 468287533 468320301).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21640 468287533 468320301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 468189229 468254765).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 468189229 ≤ 468221997)
    (by decide : 468221997 ≤ 468254765) block0 block1

theorem join_0_1 : (twinPrimeSegment 468254765 468320301).card = 191 := by
  simpa using combineTwinPrimeSegments (by decide : 468254765 ≤ 468287533)
    (by decide : 468287533 ≤ 468320301) block2 block3

theorem join_1_0 : (twinPrimeSegment 468189229 468320301).card = 410 := by
  simpa using combineTwinPrimeSegments (by decide : 468189229 ≤ 468254765)
    (by decide : 468254765 ≤ 468320301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 468189229 468320301).card = 410 := join_1_0

end S223C04
end Sude.GeneratedTwinScan
