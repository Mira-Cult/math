import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16540)) 273547309 273580077 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 273547309 273580077).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16540 273547309 273580077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16541)) 273580077 273612845 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 273580077 273612845).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16541 273580077 273612845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16542)) 273612845 273645613 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 273612845 273645613).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16542 273612845 273645613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16543)) 273645613 273678381 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 273645613 273678381).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16543 273645613 273678381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 273547309 273612845).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 273547309 ≤ 273580077)
    (by decide : 273580077 ≤ 273612845) block0 block1

theorem join_0_1 : (twinPrimeSegment 273612845 273678381).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 273612845 ≤ 273645613)
    (by decide : 273645613 ≤ 273678381) block2 block3

theorem join_1_0 : (twinPrimeSegment 273547309 273678381).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 273547309 ≤ 273612845)
    (by decide : 273612845 ≤ 273678381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 273547309 273678381).card = 458 := join_1_0

end S130C07
end Sude.GeneratedTwinScan
