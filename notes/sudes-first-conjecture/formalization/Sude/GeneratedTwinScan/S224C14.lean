import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21717)) 471597101 471629869 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 471597101 471629869).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21717 471597101 471629869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21717)) 471629869 471662637 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 471629869 471662637).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21717 471629869 471662637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21718)) 471662637 471695405 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 471662637 471695405).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21718 471662637 471695405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21719)) 471695405 471728173 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 471695405 471728173).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21719 471695405 471728173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 471597101 471662637).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 471597101 ≤ 471629869)
    (by decide : 471629869 ≤ 471662637) block0 block1

theorem join_0_1 : (twinPrimeSegment 471662637 471728173).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 471662637 ≤ 471695405)
    (by decide : 471695405 ≤ 471728173) block2 block3

theorem join_1_0 : (twinPrimeSegment 471597101 471728173).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 471597101 ≤ 471662637)
    (by decide : 471662637 ≤ 471728173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 471597101 471728173).card = 458 := join_1_0

end S224C14
end Sude.GeneratedTwinScan
