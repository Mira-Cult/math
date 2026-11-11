import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14747)) 217448493 217481261 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 217448493 217481261).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14747 217448493 217481261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14748)) 217481261 217514029 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 217481261 217514029).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14748 217481261 217514029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14749)) 217514029 217546797 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 217514029 217546797).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14749 217514029 217546797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14750)) 217546797 217579565 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 217546797 217579565).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14750 217546797 217579565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 217448493 217514029).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 217448493 ≤ 217481261)
    (by decide : 217481261 ≤ 217514029) block0 block1

theorem join_0_1 : (twinPrimeSegment 217514029 217579565).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 217514029 ≤ 217546797)
    (by decide : 217546797 ≤ 217579565) block2 block3

theorem join_1_0 : (twinPrimeSegment 217448493 217579565).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 217448493 ≤ 217514029)
    (by decide : 217514029 ≤ 217579565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 217448493 217579565).card = 463 := join_1_0

end S103C11
end Sude.GeneratedTwinScan
