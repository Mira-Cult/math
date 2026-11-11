import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20400)) 416153645 416186413 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 416153645 416186413).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20400 416153645 416186413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20401)) 416186413 416219181 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 416186413 416219181).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20401 416186413 416219181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20402)) 416219181 416251949 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 416219181 416251949).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20402 416219181 416251949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20403)) 416251949 416284717 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 416251949 416284717).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20403 416251949 416284717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 416153645 416219181).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 416153645 ≤ 416186413)
    (by decide : 416186413 ≤ 416219181) block0 block1

theorem join_0_1 : (twinPrimeSegment 416219181 416284717).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 416219181 ≤ 416251949)
    (by decide : 416251949 ≤ 416284717) block2 block3

theorem join_1_0 : (twinPrimeSegment 416153645 416284717).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 416153645 ≤ 416219181)
    (by decide : 416219181 ≤ 416284717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 416153645 416284717).card = 449 := join_1_0

end S198C07
end Sude.GeneratedTwinScan
