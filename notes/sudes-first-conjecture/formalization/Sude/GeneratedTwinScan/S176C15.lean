import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19263)) 371064877 371097645 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 371064877 371097645).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19263 371064877 371097645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19264)) 371097645 371130413 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 371097645 371130413).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19264 371097645 371130413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19265)) 371130413 371163181 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 371130413 371163181).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19265 371130413 371163181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19266)) 371163181 371195949 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 371163181 371195949).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19266 371163181 371195949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 371064877 371130413).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 371064877 ≤ 371097645)
    (by decide : 371097645 ≤ 371130413) block0 block1

theorem join_0_1 : (twinPrimeSegment 371130413 371195949).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 371130413 ≤ 371163181)
    (by decide : 371163181 ≤ 371195949) block2 block3

theorem join_1_0 : (twinPrimeSegment 371064877 371195949).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 371064877 ≤ 371130413)
    (by decide : 371130413 ≤ 371195949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 371064877 371195949).card = 434 := join_1_0

end S176C15
end Sude.GeneratedTwinScan
