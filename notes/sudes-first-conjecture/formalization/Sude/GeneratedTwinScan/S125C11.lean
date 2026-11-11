import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16236)) 263585837 263618605 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 263585837 263618605).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16236 263585837 263618605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16237)) 263618605 263651373 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 263618605 263651373).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16237 263618605 263651373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16238)) 263651373 263684141 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 263651373 263684141).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16238 263651373 263684141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16239)) 263684141 263716909 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 263684141 263716909).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16239 263684141 263716909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 263585837 263651373).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 263585837 ≤ 263618605)
    (by decide : 263618605 ≤ 263651373) block0 block1

theorem join_0_1 : (twinPrimeSegment 263651373 263716909).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 263651373 ≤ 263684141)
    (by decide : 263684141 ≤ 263716909) block2 block3

theorem join_1_0 : (twinPrimeSegment 263585837 263716909).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 263585837 ≤ 263651373)
    (by decide : 263651373 ≤ 263716909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 263585837 263716909).card = 456 := join_1_0

end S125C11
end Sude.GeneratedTwinScan
