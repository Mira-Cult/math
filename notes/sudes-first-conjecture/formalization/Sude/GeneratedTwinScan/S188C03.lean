import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19866)) 394657837 394690605 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 394657837 394690605).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19866 394657837 394690605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19867)) 394690605 394723373 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 394690605 394723373).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19867 394690605 394723373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19868)) 394723373 394756141 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 394723373 394756141).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19868 394723373 394756141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19869)) 394756141 394788909 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 394756141 394788909).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19869 394756141 394788909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 394657837 394723373).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 394657837 ≤ 394690605)
    (by decide : 394690605 ≤ 394723373) block0 block1

theorem join_0_1 : (twinPrimeSegment 394723373 394788909).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 394723373 ≤ 394756141)
    (by decide : 394756141 ≤ 394788909) block2 block3

theorem join_1_0 : (twinPrimeSegment 394657837 394788909).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 394657837 ≤ 394723373)
    (by decide : 394723373 ≤ 394788909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 394657837 394788909).card = 482 := join_1_0

end S188C03
end Sude.GeneratedTwinScan
