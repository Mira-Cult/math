import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15492)) 239992877 240025645 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 239992877 240025645).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15492 239992877 240025645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15493)) 240025645 240058413 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 240025645 240058413).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15493 240025645 240058413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15494)) 240058413 240091181 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 240058413 240091181).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15494 240058413 240091181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15495)) 240091181 240123949 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 240091181 240123949).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15495 240091181 240123949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 239992877 240058413).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 239992877 ≤ 240025645)
    (by decide : 240025645 ≤ 240058413) block0 block1

theorem join_0_1 : (twinPrimeSegment 240058413 240123949).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 240058413 ≤ 240091181)
    (by decide : 240091181 ≤ 240123949) block2 block3

theorem join_1_0 : (twinPrimeSegment 239992877 240123949).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 239992877 ≤ 240058413)
    (by decide : 240058413 ≤ 240123949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 239992877 240123949).card = 455 := join_1_0

end S114C07
end Sude.GeneratedTwinScan
