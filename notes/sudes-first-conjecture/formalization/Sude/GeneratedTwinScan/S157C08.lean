import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18175)) 330301485 330334253 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 330301485 330334253).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18175 330301485 330334253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18176)) 330334253 330367021 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 330334253 330367021).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18176 330334253 330367021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18176)) 330367021 330399789 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 330367021 330399789).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18176 330367021 330399789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18177)) 330399789 330432557 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 330399789 330432557).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18177 330399789 330432557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 330301485 330367021).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 330301485 ≤ 330334253)
    (by decide : 330334253 ≤ 330367021) block0 block1

theorem join_0_1 : (twinPrimeSegment 330367021 330432557).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 330367021 ≤ 330399789)
    (by decide : 330399789 ≤ 330432557) block2 block3

theorem join_1_0 : (twinPrimeSegment 330301485 330432557).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 330301485 ≤ 330367021)
    (by decide : 330367021 ≤ 330432557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 330301485 330432557).card = 471 := join_1_0

end S157C08
end Sude.GeneratedTwinScan
