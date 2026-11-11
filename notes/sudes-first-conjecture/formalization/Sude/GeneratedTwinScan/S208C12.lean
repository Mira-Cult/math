import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20923)) 437780525 437813293 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 437780525 437813293).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20923 437780525 437813293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20924)) 437813293 437846061 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 437813293 437846061).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20924 437813293 437846061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20925)) 437846061 437878829 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 437846061 437878829).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20925 437846061 437878829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20926)) 437878829 437911597 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 437878829 437911597).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20926 437878829 437911597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 437780525 437846061).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 437780525 ≤ 437813293)
    (by decide : 437813293 ≤ 437846061) block0 block1

theorem join_0_1 : (twinPrimeSegment 437846061 437911597).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 437846061 ≤ 437878829)
    (by decide : 437878829 ≤ 437911597) block2 block3

theorem join_1_0 : (twinPrimeSegment 437780525 437911597).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 437780525 ≤ 437846061)
    (by decide : 437846061 ≤ 437911597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 437780525 437911597).card = 434 := join_1_0

end S208C12
end Sude.GeneratedTwinScan
