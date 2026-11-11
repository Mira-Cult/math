import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22722)) 516292653 516325421 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 516292653 516325421).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22722 516292653 516325421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22723)) 516325421 516358189 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 516325421 516358189).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22723 516325421 516358189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22724)) 516358189 516390957 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 516358189 516390957).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22724 516358189 516390957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22724)) 516390957 516423725 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 516390957 516423725).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22724 516390957 516423725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 516292653 516358189).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 516292653 ≤ 516325421)
    (by decide : 516325421 ≤ 516358189) block0 block1

theorem join_0_1 : (twinPrimeSegment 516358189 516423725).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 516358189 ≤ 516390957)
    (by decide : 516390957 ≤ 516423725) block2 block3

theorem join_1_0 : (twinPrimeSegment 516292653 516423725).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 516292653 ≤ 516358189)
    (by decide : 516358189 ≤ 516423725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 516292653 516423725).card = 434 := join_1_0

end S246C03
end Sude.GeneratedTwinScan
