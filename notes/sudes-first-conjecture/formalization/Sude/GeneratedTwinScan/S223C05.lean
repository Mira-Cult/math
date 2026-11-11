import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21641)) 468320301 468353069 = 94 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 468320301 468353069).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21641 468320301 468353069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21642)) 468353069 468385837 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 468353069 468385837).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21642 468353069 468385837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21642)) 468385837 468418605 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 468385837 468418605).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21642 468385837 468418605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21643)) 468418605 468451373 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 468418605 468451373).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21643 468418605 468451373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 468320301 468385837).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 468320301 ≤ 468353069)
    (by decide : 468353069 ≤ 468385837) block0 block1

theorem join_0_1 : (twinPrimeSegment 468385837 468451373).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 468385837 ≤ 468418605)
    (by decide : 468418605 ≤ 468451373) block2 block3

theorem join_1_0 : (twinPrimeSegment 468320301 468451373).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 468320301 ≤ 468385837)
    (by decide : 468385837 ≤ 468451373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 468320301 468451373).card = 414 := join_1_0

end S223C05
end Sude.GeneratedTwinScan
