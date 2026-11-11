import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21614)) 467140653 467173421 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 467140653 467173421).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21614 467140653 467173421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21614)) 467173421 467206189 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 467173421 467206189).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21614 467173421 467206189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21615)) 467206189 467238957 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 467206189 467238957).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21615 467206189 467238957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21616)) 467238957 467271725 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 467238957 467271725).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21616 467238957 467271725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 467140653 467206189).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 467140653 ≤ 467173421)
    (by decide : 467173421 ≤ 467206189) block0 block1

theorem join_0_1 : (twinPrimeSegment 467206189 467271725).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 467206189 ≤ 467238957)
    (by decide : 467238957 ≤ 467271725) block2 block3

theorem join_1_0 : (twinPrimeSegment 467140653 467271725).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 467140653 ≤ 467206189)
    (by decide : 467206189 ≤ 467271725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 467140653 467271725).card = 421 := join_1_0

end S222C12
end Sude.GeneratedTwinScan
