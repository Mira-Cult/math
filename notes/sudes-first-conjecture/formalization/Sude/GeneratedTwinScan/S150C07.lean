import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17762)) 315490349 315523117 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 315490349 315523117).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17762 315490349 315523117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17763)) 315523117 315555885 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 315523117 315555885).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17763 315523117 315555885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17764)) 315555885 315588653 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 315555885 315588653).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17764 315555885 315588653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17765)) 315588653 315621421 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 315588653 315621421).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17765 315588653 315621421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 315490349 315555885).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 315490349 ≤ 315523117)
    (by decide : 315523117 ≤ 315555885) block0 block1

theorem join_0_1 : (twinPrimeSegment 315555885 315621421).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 315555885 ≤ 315588653)
    (by decide : 315588653 ≤ 315621421) block2 block3

theorem join_1_0 : (twinPrimeSegment 315490349 315621421).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 315490349 ≤ 315555885)
    (by decide : 315555885 ≤ 315621421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 315490349 315621421).card = 482 := join_1_0

end S150C07
end Sude.GeneratedTwinScan
